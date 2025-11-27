//  IDENT.rs
//    by Lut99
//
//  Description:
//!   Implements our optimized identifiers.
//

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{BuildHasher as _, Hash, Hasher};

use ast_toolkit::span::{Span, Spanning};
use fxhash::FxBuildHasher;
use hashbrown::HashTable;
use parking_lot::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};


/***** GLOBALS *****/
/// The hasher we use to build the identifier names.
static IDENT_NAMES_HASHER: Mutex<FxBuildHasher> = Mutex::new(FxBuildHasher::new());
/// The table of identifier uniqueness values to their string values.
static IDENT_NAMES_TABLE: RwLock<HashTable<(u64, String)>> = RwLock::new(HashTable::new());





/***** AUXILLARY *****/
/// Lock for the global table to be able to bundle the creation of multiple identifiers.
pub struct IdentFactory {
    /// A lock to the global hasher.
    hasher: MutexGuard<'static, FxBuildHasher>,
    /// A lock to the global table.
    table:  RwLockWriteGuard<'static, HashTable<(u64, String)>>,
}

// Identifier lock
impl IdentFactory {
    /// Creates a new [`Ident`]ifier, updating the global table with the hash -> name maps.
    ///
    /// This can be used to do multiple constructions of [`Ident`]ifiers in one go. If you don't
    /// need or want to explicitly bundle everything in one lock, then instead use [`Ident::new()`]
    /// to lock the global table once and only for that creation.
    ///
    /// # Arguments
    /// - `value`: The value of the string identifier.
    /// - `span`: An (optional) [`Span`] that relates this identifier to the source text.
    ///
    /// # Returns
    /// A new Ident that can be used for efficient reasoning.
    #[inline]
    pub fn create<S>(&mut self, value: String, span: Option<Span<S>>) -> Ident<S> {
        // First, hash the value and insert the mapping
        let hash: u64 = self.hasher.hash_one(&value);
        if self.table.find(hash, |(h, _)| *h == hash).is_none() {
            self.table.insert_unique(hash, (hash, value), |(h, _)| *h);
        }

        // Now construct self
        Ident { uniqueness: hash, span }
    }
}



/// Lock for the global table to be able to bundle the reading of multiple identifiers.
pub struct IdentViewer {
    /// A lock to the global table.
    table: RwLockReadGuard<'static, HashTable<(u64, String)>>,
}

// Identifier lock
impl IdentViewer {
    /// Reads the value of an [`Ident`]ifier.
    ///
    /// This can be used to do multiple reads of [`Ident`]ifier values in one go. If you don't
    /// need or want to explicitly bundle everything in one lock, then instead use
    /// [`Ident::value()`] to lock the global table once and only for that creation.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`]ifier to return the value of.
    ///
    /// # Returns
    /// A reference to the string value of the given `ident`ifier.
    ///
    /// # Panics
    /// This function will panic if, somehow, the given `ident`ifier does not exist in the global
    /// table.
    #[inline]
    pub fn value_of<S>(&self, ident: &Ident<S>) -> &str {
        self.table
            .find(ident.uniqueness, |(h, _)| *h == ident.uniqueness)
            .unwrap_or_else(|| panic!("Identifier with hash {} is not in the global name table", ident.uniqueness))
            .1
            .as_str()
    }
}





/***** LIBRARY *****/
/// Defines compressed identifiers that are cheap to carry around and compare.
#[derive(Clone, Copy, better_derive::Debug)]
pub struct Ident<S> {
    /// Determines the "uniqueness" of the Ident. This is what we use to compare and hash.
    uniqueness: u64,
    /// The location where we found this Ident in the source text.
    span: Option<Span<S>>,
}

// Constructors
impl<S> Ident<S> {
    /// Constructor for the Ident that injects the given string in the global string table.
    ///
    /// Take note that this means a lock is acquired on a global data structure. Hence, calling
    /// this operation from multiple threads at the same time may be relatively expensive.
    /// Similarly, if you are calling this operation multiple times in a row, it may be more
    /// efficient to get a global lock using [`Ident::factory()`] to create a single lock and
    /// create multiple identifiers with it.
    ///
    /// # Arguments
    /// - `value`: The value of the string identifier.
    /// - `span`: An (optional) [`Span`] that relates this identifier to the source text.
    ///
    /// # Returns
    /// A new Ident that can be used for efficient reasoning.
    #[inline]
    pub fn new(value: String, span: Option<Span<S>>) -> Self { Self::factory().create(value, span) }
}

// Locks
impl<S> Ident<S> {
    /// Acquires the global lock once as a write lock, then returns an [`IdentFactory`] that can be
    /// used to create multiple identifiers efficiently.
    ///
    /// If you don't need to do it multiple times, consider using [`Ident::new()`] for simplicity.
    ///
    /// # Returns
    /// A new [`IdentFactory`] that can [`IdentFactory::create()`].
    #[inline]
    pub fn factory() -> IdentFactory { IdentFactory { hasher: IDENT_NAMES_HASHER.lock(), table: IDENT_NAMES_TABLE.write() } }

    /// Acquires the global lock once as a read lock, then returns an [`IdentViewer`] that can be
    /// used to get the [`Ident::value()`] of multiple identifiers efficiently (and as reference).
    ///
    /// If you don't need to do it multiple times, or if you want an owned version anyway, consider
    /// using [`Ident::value()`] for simplicity.
    ///
    /// # Returns
    /// A new [`IdentViewer`] that can [`IdentViewer::value_of()`].
    #[inline]
    pub fn viewer() -> IdentViewer { IdentViewer { table: IDENT_NAMES_TABLE.read() } }
}

// Ops
impl<S> Display for Ident<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let viewer = Self::viewer();
        write!(f, "{}", viewer.value_of(self))
    }
}
impl<S> Eq for Ident<S> {}
impl<S> Hash for Ident<S> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) { self.uniqueness.hash(state); }
}
impl<S> Ord for Ident<S> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Get a global lock and both names
        let viewer = Self::viewer();
        let lhs: &str = viewer.value_of(self);
        let rhs: &str = viewer.value_of(other);

        // Compare
        lhs.cmp(rhs)
    }
}
impl<S> PartialEq for Ident<S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.uniqueness == other.uniqueness }
}
impl<S> PartialOrd for Ident<S> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

// Accessors
impl<S> Ident<S> {
    /// Returns the value of this identifier as a string.
    ///
    /// This will access the global hash -> name table to turn the hash in this type into the
    /// original name. If you do this operation many times in a row, consider using
    /// [`Ident::viewer()`] instead to lock only once and to get references out of it.
    ///
    /// # Returns
    /// A [`String`] value of this Identifier. Note that it's owned as the global lock is released
    /// instantly.
    #[inline]
    pub fn value(&self) -> String { Self::viewer().value_of(self).into() }

    /// Returns the inner [`Span`] for read-only access.
    ///
    /// # Returns
    /// A reference to the [`Span`] that relates this identifier to the source text, if any.
    #[inline]
    pub const fn span(&self) -> &Option<Span<S>> { &self.span }

    /// Returns the inner [`Span`] mutably.
    ///
    /// # Returns
    /// A mutable reference to the [`Span`] that relates this identifier to the source text, if any.
    #[inline]
    pub const fn span_mut(&mut self) -> &mut Option<Span<S>> { &mut self.span }
}
impl<S: Clone> Spanning<S> for Ident<S> {
    #[inline]
    fn get_span(&self) -> Option<Cow<'_, Span<S>>> { self.span.as_ref().map(Cow::Borrowed) }

    #[inline]
    fn take_span(self) -> Option<Span<S>> { self.span }
}
