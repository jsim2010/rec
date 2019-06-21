//! Implements base items used throughout `rec`.
use regex::Regex;
use std::{
    fmt::{self, Debug, Display, Formatter},
    ops::{Add, BitOr},
};

/// A struct that can be converted into a [`Rec`].
pub trait Element: Add<Rec, Output = Rec> + BitOr<Rec, Output = Rec> + Debug + PartialEq<Rec> {
    /// Converts `self` to a [`String`] that is compatible with [`regex`].
    fn to_regex(&self) -> String;

    /// Converts `self` to a [`String`] compatible with [`regex`] representing a single element.
    ///
    /// By default, returns `to_regex`. [`Element`]s that require grouping should handle this special
    /// case.
    fn to_group(&self) -> String {
        self.to_regex()
    }

    /// Converts `self` to a [`Rec`].
    fn to_rec(&self) -> Rec {
        Rec(self.to_regex())
    }

    /// Creates a `Rec` consisting of `other` appended to `self`.
    fn append(&self, other: &dyn Element) -> Rec {
        Rec(format!("{}{}", self.to_regex(), other.to_regex()))
    }

    /// Creates a `Rec` consisting of an alternation of `self` and `other` .
    fn alternate(&self, other: &dyn Element) -> Rec {
        Rec(format!("(?:{}|{})", self.to_regex(), other.to_regex()))
    }
}





/// Constructs a regular expression.
///
/// Works as a simple wrapper around a String to which additional [`Element`]s can be appended.
/// This implements the Builder pattern for [`Regex`].
#[derive(Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Rec(String);

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
        Regex::new(&self.0)
    }
}

impl<Rhs: Element> Add<Rhs> for Rec {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Rhs) -> Self {
        self.append(&rhs)
    }
}

impl<T: Element> BitOr<T> for Rec {
    type Output = Self;

    #[inline]
    /// Sets lhs and rhs as possible alternatives.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!("a" + (Class::Digit | ("b" + Class::Whitespace)) + "c", Rec::from(r"a(?:\d|b\s)c"));
    /// ```
    fn bitor(self, rhs: T) -> Self {
        self.alternate(&rhs)
    }
}

impl Display for Rec {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Element for Rec {
    fn to_regex(&self) -> String {
        self.0.clone()
    }

    fn to_group(&self) -> String {
        format!("(?:{})", self.to_regex())
    }
}

impl From<&str> for Rec {
    fn from(other: &str) -> Self {
        Rec(String::from(other))
    }
}

impl Add<Rec> for char {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.append(&rhs)
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
        self.to_regex() == other.to_regex()
    }
}

impl PartialEq<Rec> for &str {
    fn eq(&self, other: &Rec) -> bool {
        self.to_regex() == other.to_regex()
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

    fn to_group(&self) -> String {
        format!("(?:{})", self.to_regex())
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.append(&rhs)
    }
}

impl BitOr<Rec> for &'_ str {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.append(&rhs)
    }
}

impl PartialEq<Rec> for String {
    fn eq(&self, other: &Rec) -> bool {
        self.to_regex() == other.to_regex()
    }
}

impl Element for String {
    fn to_regex(&self) -> String {
        self.clone()
    }

    fn to_group(&self) -> String {
        format!("(?:{})", self.to_regex())
    }
}

impl Add<Rec> for String {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Self::Output {
        self.append(&rhs)
    }
}

impl BitOr<Rec> for String {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}
