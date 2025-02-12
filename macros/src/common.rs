//  COMMON.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 10:47:06
//  Last edited:
//    12 Feb 2025, 15:49:00
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines common code between the two macros.
//

use proc_macro2::{Delimiter, Span, TokenStream as TokenStream2, TokenTree};
use quote::{ToTokens, quote, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned as _;
use syn::token::{Colon, Comma, Dot, Minus, Override, Paren, PathSep, Virtual};
use syn::{Attribute, Error, Expr, ExprLit, Ident, Lit, LitStr, Meta, Path, PathArguments, PathSegment, Token, parenthesized};


/***** CONSTANTS *****/
/// Defines the placeholder for the crate path while generating tokens. It will later be
/// overwritten with the actual crate path.
pub type CratePath = Override;

/// Defines the placeholder for the crate path while generating tokens. It will later be
/// overwritten with the actual from string.
pub type FromStr = Virtual;





/***** HELPER FUNCTIONS *****/
/// Parses a comma-separated list of comma's as long as it's nice.
///
/// # Arguments
/// - `input`: The [`ParseStream`] to parse from.
/// - `what`: Another parser that represents the values in the list.
///
/// # Returns
/// A [`Punctuated`] that contains the parsed elements.
///
/// # Errors
/// This function errors if we failed to parse at all.
pub fn parse_punctuated<T>(input: ParseStream, what: fn(input: ParseStream) -> Result<T, Error>) -> Result<Punctuated<T, Comma>, Error> {
    // See if we can parse a value
    let mut res: Punctuated<T, Comma> = Punctuated::new();
    while let Ok(val) = what(input) {
        res.push_value(val);

        // Attempt to parse an punctuation
        if let Ok(punct) = input.parse::<Comma>() {
            res.push_punct(punct);
        }
    }
    Ok(res)
}

/// Serializes a punctuated list to one build manually after generation.
///
/// # Arguments
/// - `what`: Another parser that represents the values in the list.
///
/// # Returns
/// A [`TokenStream2`] that contains the serialized tokens.
pub fn serialize_punctuated<T: ToTokens>(items: impl IntoIterator<Item = T>) -> TokenStream2 {
    let (crate_path, from_str): (CratePath, FromStr) = Default::default();

    let mut items = items.into_iter().peekable();
    let first_span: Span = items.peek().expect("Got empty consequence list").span();
    let mut tokens_punct: TokenStream2 = TokenStream2::new();
    for (i, items) in items.enumerate() {
        if i == 0 {
            tokens_punct.extend(quote_spanned! { items.span() => punct.push_first(#items); });
        } else {
            tokens_punct.extend(
                quote_spanned! { items.span() => punct.push(#crate_path::ast::Comma{ span: #crate_path::ast::Span::new(#from_str, ",") }, #items); },
            );
        }
    }
    quote_spanned! { first_span => { let mut punct = #crate_path::ast::Punctuated::new(); #tokens_punct punct } }
}





/***** ATTRIBUTES *****/
/// Defines the attributes we parse from the toplevel.
pub struct DatalogAttributes {
    /// The initial path to use to refer to the crate.
    pub crate_path: Path,
    /// The string used as `from`.
    pub from: LitStr,
}
impl Parse for DatalogAttributes {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Attempt to parse an attribute thingy first
        let attrs: Vec<Attribute> = Attribute::parse_inner(input)?;

        // Create a sensible default
        let mut segments: Punctuated<PathSegment, PathSep> = Punctuated::new();
        segments.push(PathSegment { ident: Ident::new("datalog", Span::call_site()), arguments: PathArguments::None });
        let mut res: Self =
            Self { crate_path: Path { leading_colon: Some(PathSep::default()), segments }, from: LitStr::new("<auto-generated>", Span::call_site()) };

        // Iterate over the attributes to deviate from the default
        for attr in attrs {
            match attr.meta {
                Meta::Path(p) => {
                    if p.is_ident("crate") {
                        // Change the path to be from within this crate
                        let mut segments: Punctuated<PathSegment, PathSep> = Punctuated::new();
                        segments.push(PathSegment { ident: Ident::new("crate", p.span()), arguments: PathArguments::None });
                        res.crate_path = Path { leading_colon: None, segments };
                    } else {
                        return Err(Error::new(p.span(), "Unknown datalog snippet attribute"));
                    }
                },
                Meta::NameValue(nv) => {
                    if nv.path.is_ident("from") {
                        // Parse the value as a string literal
                        let from: LitStr = if let Expr::Lit(ExprLit { attrs: _, lit: Lit::Str(from) }) = nv.value {
                            from
                        } else {
                            return Err(Error::new(nv.value.span(), "Expected a string literal"));
                        };

                        // Set it
                        res.from = from;
                    } else if nv.path.is_ident("crate") {
                        // Parse the value as a string literal first
                        let from: LitStr = if let Expr::Lit(ExprLit { attrs: _, lit: Lit::Str(from) }) = nv.value {
                            from
                        } else {
                            return Err(Error::new(nv.value.span(), "Expected a string literal"));
                        };

                        // Then parse it as a path segment
                        res.crate_path = match syn::parse_str(&from.value()) {
                            Ok(path) => path,
                            Err(err) => return Err(err),
                        };

                        // Set it
                        res.from = from;
                    } else {
                        return Err(Error::new(nv.path.span(), "Unknown datalog snippet attribute"));
                    }
                },
                Meta::List(l) => return Err(Error::new(l.path.span(), "Unknown datalog snippet attribute")),
            }
        }

        // Done!
        Ok(res)
    }
}





/***** AST *****/
/// Defines the macro's representation of a rule.
pub struct Rule {
    /// The bunch of consequents.
    pub consequents: Punctuated<Atom, Comma>,
    /// The optional list of antecedents.
    pub antecedents: Option<((Colon, Minus), Punctuated<Literal, Comma>)>,
}
impl Parse for Rule {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse the consequences
        let consequents = parse_punctuated(input, Atom::parse)?;
        if consequents.is_empty() {
            return Err(input.error("Expected at least one consequent"));
        }

        // Parse the antecedents, if any
        let antecedents = if let (Ok(colon), Ok(minus)) = (input.parse::<Colon>(), input.parse::<Minus>()) {
            // Parse a punctuated list of antecedents
            let antecedents: Punctuated<Literal, Comma> = parse_punctuated(input, Literal::parse)?;
            if antecedents.is_empty() {
                return Err(input.error("Expected at least one antecedent"));
            }
            Some(((colon, minus), antecedents))
        } else {
            None
        };

        // Parse the final dot
        let _dot: Dot = input.parse()?;

        // Done parsing!
        Ok(Self { consequents, antecedents })
    }
}
impl ToTokens for Rule {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // First, generate consequences
        let consequents_tokens: TokenStream2 = serialize_punctuated(self.consequents.iter());

        // Next, generate the antecedents
        let antecedents_tokens: TokenStream2 = if let Some(((colon, _), antecedents)) = &self.antecedents {
            // Generate all the antecedents
            let antecedents_tokens: TokenStream2 = serialize_punctuated(antecedents.iter());

            // Serialize them to a single RuleBody
            quote_spanned! {
                colon.span =>
                Some(#crate_path::ast::RuleBody {
                    arrow_token: #crate_path::ast::Arrow { span: #crate_path::ast::Span::new(#from_str, ":-") },
                    antecedents: #antecedents_tokens,
                })
            }
        } else {
            quote_spanned! { consequents_tokens.span() => None }
        };

        // Finally, serialize the rule!
        tokens.extend(quote_spanned! {
            consequents_tokens.span() =>
            #crate_path::ast::Rule {
                consequents: #consequents_tokens,
                tail: #antecedents_tokens,
                dot: #crate_path::ast::Dot { span: #crate_path::ast::Span::new(#from_str, ".") },
            }
        });
    }
}

/// Defines the macro's representation of a literal (e.g., an antecedent).
pub struct Literal {
    /// The optional negative keyword.
    pub not:  Option<Ident>,
    /// The rest of the atom.
    pub atom: Atom,
}
impl Parse for Literal {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse an atom first
        let atom: Atom = input.parse()?;

        // If that atom happens to be an argumentless fact called 'not', then try again
        let (not, atom): (Option<Ident>, Atom) = if let Atom::Fact { ident, args } = atom {
            if ident == "not" && args.is_none() { (Some(ident), input.parse()?) } else { (None, Atom::Fact { ident, args }) }
        } else {
            (None, atom)
        };

        // OK
        Ok(Self { not, atom })
    }
}
impl ToTokens for Literal {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // Generate the consequent atom
        let span: Span = self.atom.span();
        let atom: &Atom = &self.atom;
        if self.not.is_some() {
            tokens.extend(quote_spanned! {
                span =>
                #crate_path::ast::Literal::NegAtom(#crate_path::ast::NegAtom {
                    not_token: #crate_path::ast::Not { span: #crate_path::ast::Span::new(#from_str, "not") },
                    atom: #atom,
                })
            });
        } else {
            tokens.extend(quote_spanned! {
                span =>
                #crate_path::ast::Literal::Atom(#atom)
            });
        }
    }
}

/// Defines the macro's representation of an atom (e.g., a consequent).
pub enum Atom {
    /// A Fact
    Fact { ident: Ident, args: Option<(Paren, Punctuated<Atom, Comma>)> },
    /// A variable
    Var { ident: Ident },
}
impl Parse for Atom {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse the first identifier
        let ident: Ident = input.parse()?;

        // Check if it's capitalized or not
        if !ident.to_string().chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
            // Parse the parenthesis, optionally
            let args: Option<(Paren, Punctuated<Atom, Comma>)> = |input: ParseStream| -> Result<(Paren, Punctuated<Atom, Comma>), Error> {
                let content;
                let paren: Paren = parenthesized!(content in input);
                let args: Punctuated<Atom, Comma> = content.parse_terminated(Atom::parse, Token![,])?;
                Ok((paren, args))
            }(input)
            .ok();

            // OK
            Ok(Self::Fact { ident, args })
        } else {
            Ok(Self::Var { ident })
        }
    }
}
impl ToTokens for Atom {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();
        match self {
            Self::Fact { ident, args } => {
                // Generate the arguments
                let (paren_span, args_tokens): (Option<Span>, TokenStream2) = if let Some((paren, args)) = args {
                    // Collect the arguments
                    let args: Vec<TokenStream2> = args.into_iter().map(Atom::to_token_stream).collect();

                    // Put them in a punctuated list
                    let mut args_tokens: TokenStream2 = TokenStream2::new();
                    for (i, arg) in args.into_iter().enumerate() {
                        if i == 0 {
                            args_tokens.extend(quote_spanned! { arg.span() => punct.push_first(#arg); });
                        } else {
                            args_tokens.extend(quote_spanned! { arg.span() => punct.push(#crate_path::ast::Comma{ span: #crate_path::ast::Span::new(#from_str, ",") }, #arg); });
                        }
                    }
                    let args_tokens: TokenStream2 =
                        quote_spanned! { Span::call_site() => { let mut punct = #crate_path::ast::Punctuated::new(); #args_tokens punct } };

                    // Serialize it to one set of arguments
                    (Some(paren.span.join()), quote_spanned! { paren.span.join() => Some(#crate_path::ast::FactArgs {
                        paren_tokens: #crate_path::ast::Parens { open: #crate_path::ast::Span::new(#from_str, "("), close: #crate_path::ast::Span::new(#from_str, ")") },
                        args: #args_tokens,
                    })})
                } else {
                    (None, quote_spanned! { ident.span() => None })
                };

                // Generate the consequent atom
                let sname: String = ident.to_string();
                tokens.extend(quote_spanned! {
                    if let Some(paren) = paren_span { ident.span().join(paren).unwrap_or_else(|| ident.span()) } else { ident.span() } =>
                    #crate_path::ast::Atom::Fact(#crate_path::ast::Fact {
                        ident: #crate_path::ast::Ident { value: #crate_path::ast::Span::new(#from_str, #sname) },
                        args: #args_tokens,
                    })
                });
            },

            Self::Var { ident } => {
                // Generate the consequent atom
                let sname: String = ident.to_string();
                tokens.extend(quote_spanned! {
                    ident.span() =>
                    #crate_path::ast::Atom::Var(#crate_path::ast::Ident { value: #crate_path::ast::Span::new(#from_str, #sname) })
                });
            },
        }
    }
}





/***** LIBRARY FUNCTIONS *****/
/// Replaces all placeholders in a tokenstream with their actual contents.
///
/// # Arguments
/// - `attrs`: The [`DatalogAttributes`] used  to replace.
/// - `stream`: The [`TokenStream2`] to replace in.
///
/// # Returns
/// A new [`TokenStream2`] that is resolved
pub fn resolve_placeholders(attrs: &DatalogAttributes, stream: TokenStream2) -> TokenStream2 {
    // Pre-serialize the tokens
    let crate_path: TokenStream2 = attrs.crate_path.to_token_stream();
    let from_str: TokenStream2 = attrs.from.to_token_stream();

    // Go through the stream to resolve
    let mut res: TokenStream2 = TokenStream2::new();
    for token in stream {
        match token {
            // Actual replacing
            TokenTree::Ident(i) => {
                if i == "override" {
                    res.extend(crate_path.clone())
                } else if i == "virtual" {
                    res.extend(from_str.clone())
                } else {
                    res.extend(i.into_token_stream())
                }
            },

            // Recursion
            TokenTree::Group(g) => {
                let inner = resolve_placeholders(attrs, g.stream());
                res.extend(match g.delimiter() {
                    Delimiter::Brace => quote! { { #inner } },
                    Delimiter::Bracket => quote! { [ #inner ] },
                    Delimiter::Parenthesis => quote! { ( #inner ) },
                    Delimiter::None => quote! { #inner },
                });
            },

            // Others
            TokenTree::Punct(p) => res.extend(p.into_token_stream()),
            TokenTree::Literal(l) => res.extend(l.into_token_stream()),
        }
    }
    res
}
