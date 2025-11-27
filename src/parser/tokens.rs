//  TOKENS.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 12:04:42
//  Last edited:
//    28 Nov 2024, 17:00:01
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for $Datalog^\neg$ keywords.
//

use std::borrow::Cow;
use std::convert::Infallible;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};
use std::marker::PhantomData;

use ast_toolkit::snack::result::{Result as SResult, SnackError};
use ast_toolkit::snack::{Combinator, ParseError, fmt, scan};
use ast_toolkit::span::{Span, Spannable, SpannableBytes, Spanning, SpanningInf, SpanningMut, SpanningRef};
use ast_toolkit::tokens::{Utf8Delimiter, Utf8Token};

use crate::ast::{Arrow, Comma, Dot, Not, Parens, ParensClose, ParensOpen};


/***** HELPER MACROS *****/
/// Implements a token parser using [`Punct`]- or [`Keyword`]-combinators.
macro_rules! token_impl {
    ($comb:ident(keyword): $tag:literal => $token:ident) => {
        #[doc = concat!("Combinator for parsing a `", $tag, "`.")]
        #[doc = ""]
        #[doc = "# Returns"]
        #[doc = concat!("A combinator that parses [`", stringify!($token), "`]s.")]
        #[doc = ""]
        #[doc = "# Fails"]
        #[doc = concat!("The returned combinator fails recoverably if the input is not `", $tag, "` or is followed by an identifier. It never fails fatally.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```rust"]
        #[doc = "use ast_toolkit::snack::Combinator as _;"]
        #[doc = "use ast_toolkit::snack::result::{Expected, Result as SResult, SnackError};"]
        #[doc = "use ast_toolkit::snack::scan::tag;"]
        #[doc = "use ast_toolkit::span::Span;"]
        #[doc = concat!("use datalog::ast::", stringify!($token), ";")]
        #[doc = concat!("use datalog::parser::tokens::{self, ", stringify!($comb), "};")]
        #[doc = ""]
        #[doc = concat!("let span1 = Span::new((\"<example>\", \"", $tag, "\"));")]
        #[doc = concat!("let span2 = Span::new((\"<example>\", \"", $tag, " foo\"));")]
        #[doc = "let span3 = Span::new((\"<example>\", \"foo\"));"]
        #[doc = concat!("let span4 = Span::new((\"<example>\", \"", $tag, "foo\"));")]
        #[doc = concat!("let mut comb = ", stringify!($comb), "();")]
        #[doc = concat!("assert_eq!(comb.parse(span1), Ok((span1.slice(", stringify!($tag), ".len()..), ", stringify!($token), " { span: Some(span1.slice(..", stringify!($tag), ".len())) })));")]
            #[doc = concat!("assert_eq!(comb.parse(span2), Ok((span2.slice(", stringify!($tag), ".len() + 1..), ", stringify!($token), "{ span: Some(span2.slice(..", stringify!($tag), ".len() + 1)) })));")]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span3),"]
        #[doc = "    Err(SnackError::Recoverable(tokens::Recoverable::Token(tag::Recoverable {"]
        #[doc = concat!("        tag: b", stringify!($tag), ",")]
        #[doc = "        is_fixable: false,"]
        #[doc = "        span: span3,"]
        #[doc = "    })))"]
        #[doc = ");"]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span4),"]
        #[doc = concat!("    Err(SnackError::Recoverable(tokens::Recoverable::Ident { span: span4.slice(", stringify!($tag), ".len()..) }))")]
        #[doc = ");"]
        #[doc = "```"]
        #[inline]
        pub const fn $comb<'s, S>() -> Keyword<$token<S>, S>
        where
            S: Clone + SpannableBytes<'s>,
        {
            Keyword { _t: PhantomData, _s: PhantomData }
        }
    };

    ($comb:ident(punct): $tag:literal => $token:ident) => {
        #[doc = concat!("Combinator for parsing a `", $tag, "`.")]
        #[doc = ""]
        #[doc = "# Returns"]
        #[doc = concat!("A combinator that parses [`", stringify!($token), "`]s.")]
        #[doc = ""]
        #[doc = "# Fails"]
        #[doc = concat!("The returned combinator fails recoverably if the input is not `", $tag, "`. It never fails fatally.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```rust"]
        #[doc = "use ast_toolkit::snack::Combinator as _;"]
        #[doc = "use ast_toolkit::snack::result::{Expected, Result as SResult, SnackError};"]
        #[doc = "use ast_toolkit::snack::scan::tag;"]
        #[doc = "use ast_toolkit::span::Span;"]
        #[doc = concat!("use datalog::ast::", stringify!($token), ";")]
        #[doc = concat!("use datalog::parser::tokens::{self, ", stringify!($comb), "};")]
        #[doc = ""]
        #[doc = concat!("let span1 = Span::new((\"<example>\", \"", $tag, "\"));")]
        #[doc = concat!("let span2 = Span::new((\"<example>\", \"", $tag, " foo\"));")]
        #[doc = "let span3 = Span::new((\"<example>\", \"foo\"));"]
        #[doc = concat!("let mut comb = ", stringify!($comb), "();")]
        #[doc = concat!("assert_eq!(comb.parse(span1), Ok((span1.slice(", stringify!($tag), ".len()..), ", stringify!($token), " { span: Some(span1.slice(..", stringify!($tag), ".len())) })));")]
        #[doc = concat!("assert_eq!(comb.parse(span2), Ok((span2.slice(", stringify!($tag), ".len() + 1..), ", stringify!($token), " { span: Some(span2.slice(..", stringify!($tag), ".len() + 1)) })));")]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span3),"]
        #[doc = "    Err(SnackError::Recoverable(tokens::Recoverable::Token(tag::Recoverable {"]
        #[doc = concat!("        tag: b", stringify!($tag), ",")]
        #[doc = "        is_fixable: false,"]
        #[doc = "        span: span3,"]
        #[doc = "    })))"]
        #[doc = ");"]
        #[doc = "```"]
        #[inline]
        pub const fn $comb<'s, S>() -> Punct<$token<S>, S>
        where
            S: Clone + SpannableBytes<'s>,
        {
            Punct { _t: PhantomData, _s: PhantomData }
        }
    };
}
pub(crate) use token_impl;



/// Implements a delimiting token parser using the [`Delim`]-combinator.
macro_rules! delim_impl {
    (__conv_kind($comb:ident, $kind:ident, punct)) => { Punct<<$comb::<S> as Utf8Delimiter<S>>::$kind, S> };
    (__conv_kind($comb:ident, $kind:ident, keyword)) => { Keyword<<$comb::<S> as Utf8Delimiter<S>>::$kind, S> };

    ($comb:ident($lcomb:ident($lkind:ident) : $ltoken:ident, $rcomb:ident($rkind:ident) : $rtoken:ident): $ltag:literal, $rtag:literal => $delim:ident) => {
        token_impl!($lcomb($lkind): $ltag => $ltoken);
        token_impl!($rcomb($rkind): $rtag => $rtoken);

        #[doc = concat!("Combinator for parsing a `", $ltag, $rtag, "`-delimited piece of input.")]
        #[doc = "# Arguments"]
        #[doc = "- `comb`: Some middle `C`ombinator to parse the things in between the delimiters."]
        #[doc = ""]
        #[doc = "# Returns"]
        #[doc = concat!("A combinator that parses [`", stringify!($ltoken), "`], then something in the middle, and then [`", stringify!($token), "`]. The result is returned as a [`", stringify!($delim), "`]")]
        #[doc = ""]
        #[doc = "# Fails"]
        #[doc = concat!("The returned combinator fails recoverably if the input does not start with `", $ltag, "` or the inner combinator fails recoverably. It fails fatally if the inner combinator does or if there is no `", $rtag, "` terminating the middle part.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```rust"]
        #[doc = "use ast_toolkit::snack::Combinator as _;"]
        #[doc = "use ast_toolkit::snack::result::{Expected, Result as SResult, SnackError};"]
        #[doc = "use ast_toolkit::snack::scan::tag;"]
        #[doc = "use ast_toolkit::span::Span;"]
        #[doc = concat!("use datalog::ast::{", stringify!($delim), ", ", stringify!($ltoken), ", ", stringify!($rtoken), "};")]
        #[doc = concat!("use datalog::parser::tokens::{self, ", stringify!($comb), "};")]
        #[doc = ""]
        #[doc = concat!("let span1 = Span::new((\"<example>\", \"", $ltag, "howdy", $rtag, "\"));")]
        #[doc = concat!("let span2 = Span::new((\"<example>\", \"", $ltag, "   howdy", $rtag, "  foo\"));")]
        #[doc = concat!("let span3 = Span::new((\"<example>\", \"foo\"));")]
        #[doc = concat!("let span4 = Span::new((\"<example>\", \"", $ltag, "foo", $rtag, "\"));")]
        #[doc = concat!("let span5 = Span::new((\"<example>\", \"", $ltag, "howdy\"));")]
        #[doc = concat!("let mut comb = ", stringify!($comb), "(tag(b\"howdy\"));")]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span1),"]
        #[doc = "    Ok(("]
        #[doc = concat!("        span1.slice(\"", $ltag, "\".len() + 5 + \"", $rtag, "\".len()..),")]
        #[doc = "        ("]
        #[doc = "            Parens {"]
        #[doc = concat!("                open:  ParensOpen { span: Some(span1.slice(..\"", $ltag, "\".len())) },")]
        #[doc = concat!("                close: ParensClose { span: Some(span1.slice(\"", $ltag, "\".len() + 5..\"", $ltag, "\".len() + 5 + \"", $rtag, "\".len())) },")]
        #[doc = "            },"]
        #[doc = concat!("            span1.slice(\"", $ltag, "\".len()..\"", $ltag, "\".len() + 5)")]
        #[doc = "        )"]
        #[doc = "    ))"]
        #[doc = ");"]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span2),"]
        #[doc = "    Ok(("]
        #[doc = concat!("        span2.slice(\"", $ltag, "\".len() + 8 + \"", $rtag, "\".len() + 2..),")]
        #[doc = "        ("]
        #[doc = "            Parens {"]
        #[doc = concat!("                open:  ParensOpen { span: Some(span2.slice(..\"", $ltag, "\".len())) },")]
        #[doc = concat!("                close: ParensClose { span: Some(span2.slice(\"", $ltag, "\".len() + 8..\"", $ltag, "\".len() + 8 + \"", $rtag, "\".len())) },")]
        #[doc = "            },"]
        #[doc = concat!("            span2.slice(\"", $ltag, "\".len() + 3..\"", $ltag, "\".len() + 8)")]
        #[doc = "        )"]
        #[doc = "    ))"]
        #[doc = ");"]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span3),"]
        #[doc = "    Err(SnackError::Recoverable(tokens::DelimRecoverable::Open(tokens::Recoverable::Token(tag::Recoverable {"]
        #[doc = concat!("        tag: b", stringify!($ltag), ",")]
        #[doc = "        is_fixable: false,"]
        #[doc = "        span: span3,"]
        #[doc = "    }))))"]
        #[doc = ");"]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span4),"]
        #[doc = "    Err(SnackError::Recoverable(tokens::DelimRecoverable::Comb(tag::Recoverable {"]
        #[doc = "        tag: b\"howdy\","]
        #[doc = "        is_fixable: false,"]
        #[doc = concat!("        span: span4.slice(\"", $ltag, "\".len()..),")]
        #[doc = "    })))"]
        #[doc = ");"]
        #[doc = "assert_eq!("]
        #[doc = "    comb.parse(span5),"]
        #[doc = "    Err(SnackError::Fatal(tokens::DelimFatal::Close(tokens::Recoverable::Token(tag::Recoverable {"]
        #[doc = concat!("        tag: b\"", $rtag, "\",")]
        #[doc = "        is_fixable: true,"]
        #[doc = concat!("        span: span5.slice(\"", $ltag, "\".len() + 5..),")]
        #[doc = "    }))))"]
        #[doc = ");"]
        #[doc = "```"]
        #[inline]
        pub const fn $comb<'s, C, S>(comb: C) -> Delim<delim_impl!(__conv_kind($delim, OpenToken, $lkind)), C, delim_impl!(__conv_kind($delim, CloseToken, $rkind)), $delim<S>, S>
        where
            S: Clone + SpannableBytes<'s>,
        {
            Delim { open: $lcomb(), comb, close: $rcomb(), _t: PhantomData, _s: PhantomData }
        }
    };
}





/***** ERRORS *****/
/// Defines recoverable errors occurring from [`Keyword`] and [`Punct`].
#[derive(better_derive::Debug, better_derive::Eq, better_derive::PartialEq, Spanning, SpanningInf, SpanningRef, SpanningMut)]
pub enum Recoverable<S> {
    /// It was follow-up by an identifier.
    Ident { span: Span<S> },
    /// We saw something else than the token keyword.
    Token(scan::tag::Recoverable<'static, u8, S>),
}
impl<S> Display for Recoverable<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Ident { .. } => write!(f, "Part of identifier"),
            Self::Token(err) => <_ as Display>::fmt(err, f),
        }
    }
}
impl<'s, S: Spannable<'s>> Error for Recoverable<S> {}
impl<'s, S: Clone + Spannable<'s>> ParseError<S> for Recoverable<S> {
    #[inline]
    fn more_might_fix(&self) -> bool {
        match self {
            Self::Ident { .. } => false,
            Self::Token(err) => err.more_might_fix(),
        }
    }

    #[inline]
    fn needed_to_fix(&self) -> Option<usize> {
        match self {
            Self::Ident { .. } => None,
            Self::Token(err) => err.needed_to_fix(),
        }
    }
}



/// Defines recoverable errors occurring from [`Delim`].
#[derive(Debug, Eq, PartialEq)]
pub enum DelimRecoverable<E1, E2> {
    /// The open token failed.
    Open(E1),
    /// The middle part failed.
    Comb(E2),
}
impl<E1, E2: Display> Display for DelimRecoverable<E1, E2> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Open(_) => write!(f, "Failed to parse open token"),
            Self::Comb(err) => <_ as Display>::fmt(err, f),
        }
    }
}
impl<'s, E1: Debug, E2: Debug + Display> Error for DelimRecoverable<E1, E2> {}
impl<'s, E1: Spanning<S>, E2: Spanning<S>, S: Clone> Spanning<S> for DelimRecoverable<E1, E2> {
    #[inline]
    fn get_span(&self) -> Option<Cow<'_, Span<S>>> {
        match self {
            Self::Open(err) => err.get_span(),
            Self::Comb(err) => err.get_span(),
        }
    }

    #[inline]
    fn take_span(self) -> Option<Span<S>> {
        match self {
            Self::Open(err) => err.take_span(),
            Self::Comb(err) => err.take_span(),
        }
    }
}
impl<'s, E1: SpanningInf<S>, E2: SpanningInf<S>, S: Clone> SpanningInf<S> for DelimRecoverable<E1, E2> {
    #[inline]
    fn span(&self) -> Cow<'_, Span<S>> {
        match self {
            Self::Open(err) => err.span(),
            Self::Comb(err) => err.span(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<S> {
        match self {
            Self::Open(err) => err.into_span(),
            Self::Comb(err) => err.into_span(),
        }
    }
}
impl<'s, E1: SpanningRef<S>, E2: SpanningRef<S>, S: Clone> SpanningRef<S> for DelimRecoverable<E1, E2> {
    #[inline]
    fn span_ref(&self) -> &Span<S> {
        match self {
            Self::Open(err) => err.span_ref(),
            Self::Comb(err) => err.span_ref(),
        }
    }
}
impl<'s, E1: SpanningMut<S>, E2: SpanningMut<S>, S: Clone> SpanningMut<S> for DelimRecoverable<E1, E2> {
    #[inline]
    fn span_mut(&mut self) -> &mut Span<S> {
        match self {
            Self::Open(err) => err.span_mut(),
            Self::Comb(err) => err.span_mut(),
        }
    }
}
impl<'s, E1: ParseError<S>, E2: ParseError<S>, S: Clone + Spannable<'s>> ParseError<S> for DelimRecoverable<E1, E2> {
    #[inline]
    fn more_might_fix(&self) -> bool {
        match self {
            Self::Open(err) => err.more_might_fix(),
            Self::Comb(err) => err.more_might_fix(),
        }
    }

    #[inline]
    fn needed_to_fix(&self) -> Option<usize> {
        match self {
            Self::Open(err) => err.needed_to_fix(),
            Self::Comb(err) => err.needed_to_fix(),
        }
    }
}



/// Defines fatal errors occurring from [`Delim`].
#[derive(Debug, Eq, PartialEq)]
pub enum DelimFatal<E1, E2> {
    /// The middle part failed.
    Comb(E1),
    /// The close token failed.
    Close(E2),
}
impl<E1: Display, E2> Display for DelimFatal<E1, E2> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Comb(err) => <_ as Display>::fmt(err, f),
            Self::Close(_) => write!(f, "Failed to parse close token"),
        }
    }
}
impl<'s, E1: Debug + Display, E2: Debug> Error for DelimFatal<E1, E2> {}
impl<'s, E1: Spanning<S>, E2: Spanning<S>, S: Clone> Spanning<S> for DelimFatal<E1, E2> {
    #[inline]
    fn get_span(&self) -> Option<Cow<'_, Span<S>>> {
        match self {
            Self::Comb(err) => err.get_span(),
            Self::Close(err) => err.get_span(),
        }
    }

    #[inline]
    fn take_span(self) -> Option<Span<S>> {
        match self {
            Self::Comb(err) => err.take_span(),
            Self::Close(err) => err.take_span(),
        }
    }
}
impl<'s, E1: SpanningInf<S>, E2: SpanningInf<S>, S: Clone> SpanningInf<S> for DelimFatal<E1, E2> {
    #[inline]
    fn span(&self) -> Cow<'_, Span<S>> {
        match self {
            Self::Comb(err) => err.span(),
            Self::Close(err) => err.span(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<S> {
        match self {
            Self::Comb(err) => err.into_span(),
            Self::Close(err) => err.into_span(),
        }
    }
}
impl<'s, E1: SpanningRef<S>, E2: SpanningRef<S>, S: Clone> SpanningRef<S> for DelimFatal<E1, E2> {
    #[inline]
    fn span_ref(&self) -> &Span<S> {
        match self {
            Self::Comb(err) => err.span_ref(),
            Self::Close(err) => err.span_ref(),
        }
    }
}
impl<'s, E1: SpanningMut<S>, E2: SpanningMut<S>, S: Clone> SpanningMut<S> for DelimFatal<E1, E2> {
    #[inline]
    fn span_mut(&mut self) -> &mut Span<S> {
        match self {
            Self::Comb(err) => err.span_mut(),
            Self::Close(err) => err.span_mut(),
        }
    }
}
impl<'s, E1: ParseError<S>, E2: ParseError<S>, S: Clone + Spannable<'s>> ParseError<S> for DelimFatal<E1, E2> {
    #[inline]
    fn more_might_fix(&self) -> bool {
        match self {
            Self::Comb(err) => err.more_might_fix(),
            Self::Close(err) => err.more_might_fix(),
        }
    }

    #[inline]
    fn needed_to_fix(&self) -> Option<usize> {
        match self {
            Self::Comb(err) => err.needed_to_fix(),
            Self::Close(err) => err.needed_to_fix(),
        }
    }
}





/***** FORMATTERS *****/
/// Describes what we expected to find for single tokens.
#[derive(Debug, Eq, PartialEq)]
pub struct ExpectsFormatter {
    token: &'static str,
}
impl Display for ExpectsFormatter {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        <Self as fmt::ExpectsFormatter>::expects_fmt(self, f, 0)
    }
}
impl fmt::ExpectsFormatter for ExpectsFormatter {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "{:?}", self.token) }
}



/// Describes what we expected to find for delimiters.
#[derive(Debug, Eq, PartialEq)]
pub struct DelimExpectsFormatter<F> {
    open:  &'static str,
    fmt:   F,
    close: &'static str,
}
impl<F: fmt::ExpectsFormatter> Display for DelimExpectsFormatter<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        <Self as fmt::ExpectsFormatter>::expects_fmt(self, f, 0)
    }
}
impl<F: fmt::ExpectsFormatter> fmt::ExpectsFormatter for DelimExpectsFormatter<F> {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult {
        write!(f, "{:?}, ", self.open)?;
        <F as fmt::ExpectsFormatter>::expects_fmt(&self.fmt, f, 0)?;
        write!(f, " and then {:?}", self.close)
    }
}





/***** COMBINATORS *****/
/// Parses tokens that need to be disambiguated from identifiers.
pub struct Keyword<T, S> {
    _t: PhantomData<T>,
    _s: PhantomData<S>,
}
impl<'s, T: Utf8Token<S>, S: Clone + SpannableBytes<'s>> Combinator<'static, 's, S> for Keyword<T, S> {
    type Output = T;
    type ExpectsFormatter = ExpectsFormatter;
    type Recoverable = Recoverable<S>;
    type Fatal = Infallible;

    #[inline]
    fn expects(&self) -> Self::ExpectsFormatter { ExpectsFormatter { token: T::TOKEN } }

    #[inline]
    fn parse(&mut self, input: Span<S>) -> SResult<Self::Output, Self::Recoverable, Self::Fatal, S> {
        // Recognize the token
        let (rem, res): (Span<S>, T) = match scan::tag(T::TOKEN.as_bytes()).parse(input) {
            Ok((rem, res)) => (rem, T::from(res)),
            Err(SnackError::Recoverable(err)) => return Err(SnackError::Recoverable(Recoverable::Token(err))),
        };

        // Then ensure no identifier follows it (without whitespace!)
        if let Ok((_, _)) =
            scan::elem("identifier character", |&b| (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'_').parse(rem.clone())
        {
            return Err(SnackError::Recoverable(Recoverable::Ident { span: rem }));
        }

        // Pop any whitespace
        let (rem, _): (Span<S>, _) = super::whitespace0().parse(rem).unwrap();
        Ok((rem, res))
    }
}



/// Parses tokens that needn't have their ends checked.
pub struct Punct<T, S> {
    _t: PhantomData<T>,
    _s: PhantomData<S>,
}
impl<'s, T: Utf8Token<S>, S: Clone + SpannableBytes<'s>> Combinator<'static, 's, S> for Punct<T, S> {
    type Output = T;
    type ExpectsFormatter = ExpectsFormatter;
    type Recoverable = Recoverable<S>;
    type Fatal = Infallible;

    #[inline]
    fn expects(&self) -> Self::ExpectsFormatter { ExpectsFormatter { token: T::TOKEN } }

    #[inline]
    fn parse(&mut self, input: Span<S>) -> SResult<Self::Output, Self::Recoverable, Self::Fatal, S> {
        // Recognize the token
        let (rem, res): (Span<S>, T) = match scan::tag(T::TOKEN.as_bytes()).parse(input) {
            Ok((rem, res)) => (rem, T::from(res)),
            Err(SnackError::Recoverable(err)) => return Err(SnackError::Recoverable(Recoverable::Token(err))),
        };

        // Pop any whitespace
        let (rem, _): (Span<S>, _) = super::whitespace0().parse(rem).unwrap();
        Ok((rem, res))
    }
}



/// Parses delimiting tokens.
pub struct Delim<D1, C, D2, T, S> {
    open:  D1,
    comb:  C,
    close: D2,
    _t:    PhantomData<T>,
    _s:    PhantomData<S>,
}
impl<'c, 's, D1, C, D2, T, S> Combinator<'c, 's, S> for Delim<D1, C, D2, T, S>
where
    D1: Combinator<'c, 's, S, Output = T::OpenToken, Fatal = Infallible>,
    C: Combinator<'c, 's, S>,
    D2: Combinator<'c, 's, S, Output = T::CloseToken, Fatal = Infallible>,
    T: Utf8Delimiter<S>,
    S: Clone + SpannableBytes<'s>,
{
    type Output = (T, C::Output);
    type ExpectsFormatter = DelimExpectsFormatter<C::ExpectsFormatter>;
    type Recoverable = DelimRecoverable<D1::Recoverable, C::Recoverable>;
    type Fatal = DelimFatal<C::Fatal, D2::Recoverable>;

    #[inline]
    fn expects(&self) -> Self::ExpectsFormatter {
        DelimExpectsFormatter {
            open:  <T::OpenToken as Utf8Token<S>>::TOKEN,
            fmt:   self.comb.expects(),
            close: <T::CloseToken as Utf8Token<S>>::TOKEN,
        }
    }

    #[inline]
    fn parse(&mut self, input: Span<S>) -> SResult<Self::Output, Self::Recoverable, Self::Fatal, S> {
        // Pop the open (it will pop whitespace)
        let (rem, open): (Span<S>, T::OpenToken) = match self.open.parse(input) {
            Ok(res) => res,
            Err(SnackError::Recoverable(err)) => return Err(SnackError::Recoverable(DelimRecoverable::Open(err))),
        };

        // Run the middle part
        let (rem, res): (Span<S>, C::Output) = match self.comb.parse(rem) {
            Ok(res) => res,
            Err(SnackError::Recoverable(err)) => return Err(SnackError::Recoverable(DelimRecoverable::Comb(err))),
            Err(SnackError::Fatal(err)) => return Err(SnackError::Fatal(DelimFatal::Comb(err))),
        };

        // Then the ending part
        let (rem, close): (Span<S>, T::CloseToken) = match self.close.parse(rem) {
            Ok(res) => res,
            Err(SnackError::Recoverable(err)) => return Err(SnackError::Fatal(DelimFatal::Close(err))),
        };

        // Done
        Ok((rem, (T::from((open, close)), res)))
    }
}





/***** LIBRARY FUNCTIONS *****/
token_impl!(arrow(punct): ":-" => Arrow);
token_impl!(comma(punct): "," => Comma);
token_impl!(dot(punct): "." => Dot);
token_impl!(not(keyword): "not" => Not);

delim_impl!(parens(parens_open(punct): ParensOpen, parens_close(punct): ParensClose): "(", ")" => Parens);
// /// Combinator for parsing parenthesis with something else in between.
// ///
// /// # Arguments
// /// - `comb`: Some other combinator that is found in between the parenthesis.
// ///
// /// # Returns
// /// A combinator that parses the parenthesis with the given `comb` in between them. Returns it as a
// /// tuple of the [`Parens`] and the result of `comb`.
// ///
// /// # Fails
// /// The returned combinator fails if the input is not parenthesis, or `comb` fails.
// ///
// /// # Example
// /// ```rust
// /// use ast_toolkit::snack::Combinator as _;
// /// use ast_toolkit::snack::result::{Expected, Result as SResult, SnackError};
// /// use ast_toolkit::snack::scan::tag;
// /// use ast_toolkit::span::Span;
// /// use datalog::ast::{Parens, ParensClose, ParensOpen};
// /// use datalog::parser::tokens::{self, parens};
// ///
// /// let span1 = Span::new(("<example>", "(howdy)"));
// /// let span2 = Span::new(("<example>", "(   howdy)  foo"));
// /// let span3 = Span::new(("<example>", "foo"));
// /// let span4 = Span::new(("<example>", "(foo)"));
// /// let span5 = Span::new(("<example>", "(foo"));
// ///
// /// let mut comb = parens(tag(b"howdy"));
// /// assert_eq!(
// ///     comb.parse(span1),
// ///     Ok((
// ///         span1.slice(7..),
// ///         (
// ///             Parens {
// ///                 open:  ParensOpen { span: Some(span1.slice(..1)) },
// ///                 close: ParensClose { span: Some(span1.slice(6..7)) },
// ///             },
// ///             span.slice(1..6)
// ///         )
// ///     ))
// /// );
// /// // assert_eq!(comb.parse(span2), Ok((span2.slice(4..), Not { span: Some(span2.slice(..4)) })));
// /// // assert_eq!(
// /// //     comb.parse(span3),
// /// //     Err(SnackError::Recoverable(tokens::Recoverable::Token(tag::Recoverable {
// /// //         tag: b"not",
// /// //         is_fixable: false,
// /// //         span: span3,
// /// //     })))
// /// // );
// /// // assert_eq!(
// /// //     comb.parse(span4),
// /// //     Err(SnackError::Recoverable(tokens::Recoverable::Ident { span: span4.slice(3..) }))
// /// // );
// /// ```
// #[inline]
// pub const fn parens<'t, 's, C, S>(comb: C) -> Parens<C, S>
// where
//     C: Combinator<'t, 's, S>,
//     S: Clone + SpannableBytes<'s>,
// {
// }
