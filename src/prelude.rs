//! Common traits and structs used throughout `rec`.
use core::{
    fmt::Debug,
    ops::{Add, BitOr},
};
use regex::Regex;

/// An item that attempts to match with a single character of the searched text.
pub trait Atom: Element {
    /// Converts `self` to a [`String`] that contains everything inside the `[]` brackets.
    fn to_part(&self) -> String;
}

/// An item that can be converted into a regular expression.
pub trait Element:
    Add<Rec, Output = Rec> + BitOr<Rec, Output = Rec> + Debug + PartialEq<Rec>
{
    /// Converts `self` to a regular expression compatible with [`regex`].
    fn to_regex(&self) -> String;

    /// Returns if `self` is an [`Atom`].
    fn is_atom(&self) -> bool;

    /// Creates a [`Rec`] consisting of the alternation of `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!('a' + (Class::Digit | ('b' + Class::Whitespace)) + 'c', Rec::from(r"a(?:\d|b\s)c"));
    /// ```
    fn alternate(&self, other: &dyn Element) -> Rec {
        Rec::alternation(vec![self.to_regex(), other.to_regex()])
    }

    /// Creates a [`Rec`] consisting of the concatenation of `self` and `other`.
    fn concatenate(&self, other: &dyn Element) -> Rec {
        Rec::concatenation(vec![self.isolate(), other.isolate()])
    }

    /// Returns if the regular expression of `self` is equal to that of `other`.
    fn is_equal(&self, other: &dyn Element) -> bool {
        self.to_regex() == other.to_regex()
    }

    /// Returns the regular expression of `self` such that it can be concatenated.
    ///
    /// By default, returns `to_regex`. Should be overriden by [`Element`]s that require grouping.
    fn isolate(&self) -> String {
        self.to_regex()
    }

    /// Returns the regular expression of `self` as a single [`Atom`].
    ///
    /// If grouping is needed, uses the non-capturing grouping mechanism.
    fn group(&self) -> String {
        if self.is_atom() {
            self.to_regex()
        } else {
            format!("(?:{})", self.to_regex())
        }
    }
}

/// Constructs a regular expression.
///
/// This implements the Builder pattern for [`Regex`].
#[derive(Debug)]
pub struct Rec {
    /// The regular expressions of the elements that make up the `Rec`.
    pub(crate) elements: Vec<String>,
    /// How `elements` are composed together.
    composition: Composition,
}

impl Rec {
    /// Builds a [`Regex`] from `self`.
    ///
    /// This is only safe to use with [`Rec`]s that are known prior to runtime. Otherwise use
    /// [`try_build`].
    ///
    /// # Panics
    /// Panics if `self` contains an invalid expression.
    #[allow(clippy::result_unwrap_used)] // Panic on error is intended.
    pub fn build(self) -> Regex {
        self.try_build().unwrap()
    }

    /// Attempts to build a [`Regex`] from `self`.
    ///
    /// This is intended to be used with [`Rec`]s that are not known prior to runtime. Otherwise
    /// use [`build`].
    pub(crate) fn try_build(&self) -> Result<Regex, regex::Error> {
        Regex::new(&self.to_regex())
    }

    /// Builds a [`Rec`] with `elements` composed by [`Composition::Alternation`].
    pub(crate) const fn alternation(elements: Vec<String>) -> Self {
        Self {
            elements,
            composition: Composition::Alternation,
        }
    }

    /// Builds a [`Rec`] with `elements` composed by [`Composition::Concatenation`].
    const fn concatenation(elements: Vec<String>) -> Self {
        Self {
            elements,
            composition: Composition::Concatenation,
        }
    }

    /// Returns all regular expressions options of `self`, which will alternate with another `Rec`.
    fn alternation_elements(self) -> Vec<String> {
        match self.composition {
            Composition::Alternation => self.elements,
            Composition::Concatenation => vec![self.to_regex()],
        }
    }
}

// This meets the Add<Rec> bound for Element.
impl<Rhs: Element> Add<Rhs> for Rec {
    type Output = Self;

    fn add(self, rhs: Rhs) -> Self::Output {
        self.concatenate(&rhs)
    }
}

// Rec | Rec is a special case so that Rec | Rec | Rec does not result in (Rec | Rec) | Rec.
impl BitOr for Rec {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut elements = self.alternation_elements();
        elements.extend(rhs.alternation_elements());
        Self::alternation(elements)
    }
}

impl BitOr<char> for Rec {
    type Output = Self;

    fn bitor(self, rhs: char) -> Self::Output {
        let mut elements = self.elements;
        elements.push(rhs.to_regex());
        Self::alternation(elements)
    }
}

impl BitOr<&str> for Rec {
    type Output = Self;

    fn bitor(self, rhs: &str) -> Self::Output {
        let mut elements = self.elements;
        elements.push(rhs.to_regex());
        Self::alternation(elements)
    }
}

impl Element for Rec {
    fn to_regex(&self) -> String {
        match self.composition {
            Composition::Concatenation => self.elements.join(""),
            Composition::Alternation => self.elements.join("|"),
        }
    }

    fn is_atom(&self) -> bool {
        false
    }

    fn isolate(&self) -> String {
        match self.composition {
            Composition::Concatenation => self.to_regex(),
            Composition::Alternation => self.group(),
        }
    }
}

impl From<&str> for Rec {
    /// Converts the regular expression in &str format to a Rec.
    ///
    /// Note that this conversion does not escape metacharacters; for that functionality use &str as an Element.
    fn from(other: &str) -> Self {
        Self::from(other.to_string())
    }
}

impl From<String> for Rec {
    fn from(other: String) -> Self {
        Self::concatenation(vec![other])
    }
}

impl<T: Element> PartialEq<T> for Rec {
    fn eq(&self, other: &T) -> bool {
        self.is_equal(other)
    }
}

/// How two or more [`Element`]s are composed together.
#[derive(Debug, PartialEq)]
enum Composition {
    /// [`Element`]s are appended in order.
    Concatenation,
    /// Each [`Element`]s is a possible match.
    ///
    /// The order of the [`Element`]s determines the order of the match attempts.
    Alternation,
}

// Cannot implement Add<Element> for char.
impl Add<Rec> for char {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl Atom for char {
    fn to_part(&self) -> String {
        match self {
            '-' => String::from(r"\-"),
            _ => self.to_string(),
        }
    }
}

// Cannot implement BitOr<Element> for char.
impl BitOr<Rec> for char {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl Element for char {
    fn to_regex(&self) -> String {
        self.to_string()
    }

    fn is_atom(&self) -> bool {
        true
    }
}

// Cannot implement PartialEq<Element> for char.
impl PartialEq<Rec> for char {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}

// Cannot implement Add<Element> for &str.
impl Add<Rec> for &str {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

// Cannot implement BitOr<Element> for &str.
impl BitOr<Rec> for &'_ str {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl Element for &str {
    fn to_regex(&self) -> String {
        regex::escape(self)
    }

    fn is_atom(&self) -> bool {
        self.parse::<char>().is_ok()
    }
}

// Cannot implement PartialEq<Element> for &str.
impl PartialEq<Rec> for &str {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}

// Cannot implement Add<Element> for String.
impl Add<Rec> for String {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

// Cannot implement BitOr<Element> for String.
impl BitOr<Rec> for String {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl Element for String {
    fn to_regex(&self) -> String {
        self.clone()
    }

    fn is_atom(&self) -> bool {
        self.parse::<char>().is_ok()
    }

    fn isolate(&self) -> String {
        self.group()
    }
}

// Cannot implement PartialEq<Element> for String.
impl PartialEq<Rec> for String {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}
