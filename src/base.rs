//! Implements base items used throughout `rec`.
use regex::Regex;
use std::{
    fmt::Debug,
    ops::{Add, BitOr},
};

/// A struct that can be converted into a [`Rec`].
pub trait Element: Add<Rec, Output = Rec> + BitOr<Rec, Output = Rec> + Debug + PartialEq<Rec> {
    /// Converts `self` to a [`String`] that is compatible with [`regex`].
    fn to_regex(&self) -> String;

    /// Creates a [`Rec`] consisting of an alternation of `self` and `other` .
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!('a' + (Class::Digit | ('b' + Class::Whitespace)) + 'c', Rec::from(r"a(?:\d|b\s)c"));
    /// ```
    fn alternate(&self, other: &dyn Element) -> Rec {
        Rec::alternation(vec![self.to_regex(), other.to_regex()])
    }

    /// Creates a [`Rec`] consisting of a concatenation of `self` and `other`.
    fn concatenate(&self, other: &dyn Element) -> Rec {
        Rec::concatenation(vec![self.isolate(), other.isolate()])
    }

    /// Returns if the Regex generated by `self` is equal to that of `other`.
    fn is_equal(&self, other: &dyn Element) -> bool {
        self.to_regex() == other.to_regex()
    }

    /// Converts `self` to a [`String`] compatible with [`regex`] representing a single element.
    ///
    /// By default, returns `to_regex`. [`Element`]s that require grouping should handle this special
    /// case.
    fn isolate(&self) -> String {
        self.to_regex()
    }

    /// Returns if `self` is an [`Atom`].
    fn is_atom(&self) -> bool {
        false
    }

    /// Contains `self` as a single [`Atom`].
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
    pub(crate) elements: Vec<String>,
    relation: Relation,
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
    #[inline]
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

    pub(crate) const fn alternation(elements: Vec<String>) -> Self {
        Self {
            elements,
            relation: Relation::Alternation,
        }
    }

    const fn concatenation(elements: Vec<String>) -> Self {
        Self {
            elements,
            relation: Relation::Concatenation,
        }
    }
}

impl<Rhs: Element> Add<Rhs> for Rec {
    type Output = Self;

    fn add(self, rhs: Rhs) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl BitOr for Rec {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut elements = match self.relation {
            Relation::Alternation => self.elements,
            Relation::Concatenation => vec![self.to_regex()],
        };
        elements.extend(match rhs.relation {
            Relation::Alternation => rhs.elements,
            Relation::Concatenation => vec![rhs.to_regex()],
        });
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
        match self.relation {
            Relation::Concatenation => self.elements.join(""),
            Relation::Alternation => self.elements.join("|"),
        }
    }

    fn isolate(&self) -> String {
        match self.relation {
            Relation::Concatenation => self.to_regex(),
            Relation::Alternation => self.group(),
        }
    }
}

impl From<&str> for Rec {
    fn from(other: &str) -> Self {
        Self::concatenation(vec![String::from(other)])
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

#[derive(Debug, PartialEq)]
enum Relation {
    Concatenation,
    Alternation,
}




impl Add<Rec> for char {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl BitOr<Rec> for char {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl PartialEq<Rec> for char {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}

impl PartialEq<Rec> for &str {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}

impl Element for &str {
    fn to_regex(&self) -> String {
        self.replace(".", r"\.")
            .replace("+", r"\+")
            .replace("*", r"\*")
            .replace("?", r"\?")
            .replace("|", r"\|")
            .replace("[", r"\[")
            .replace("]", r"\]")
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl BitOr<Rec> for &'_ str {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl PartialEq<Rec> for String {
    fn eq(&self, other: &Rec) -> bool {
        self.is_equal(other)
    }
}

impl Element for String {
    fn to_regex(&self) -> String {
        self.clone()
    }

    fn isolate(&self) -> String {
        self.group()
    }
}

impl Add<Rec> for String {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl BitOr<Rec> for String {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}
