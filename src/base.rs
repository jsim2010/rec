//! Implements base items used throughout `rec`.
use crate::Pattern;
use lazy_static::lazy_static;
use regex::Regex;
use std::{fmt::{self, Display, Formatter}, ops::{Add, BitOr, RangeInclusive}};

/// Signifies elements that can be converted into a [`Rec`].
pub trait Element: Add<Rec> + BitOr<Rec> + PartialEq<Rec> {
    /// Converts `self` into a [`Rec`].
    fn into_rec(self) -> Rec;

    /// Converts `self` into a [`Rec`] that is grouped.
    fn group(self) -> Rec
    where
        Self: Sized,
    {
        self.into_rec().group()
    }
}

impl PartialEq<Rec> for &str {
    fn eq(&self, other: &Rec) -> bool {
        self.into_rec() == *other
    }
}

impl Element for &str {
    #[inline]
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// assert_eq!(".+*?|[]", Rec::from(r"\.\+\*\?\|\[\]"));
    /// ```
    fn into_rec(self) -> Rec {
        Rec(self
            .replace(".", r"\.")
            .replace("+", r"\+")
            .replace("*", r"\*")
            .replace("?", r"\?")
            .replace("|", r"\|")
            .replace("[", r"\[")
            .replace("]", r"\]"))
    }
}

impl Add<Rec> for RangeInclusive<char> {
    type Output = Rec;

    fn add(self, rhs: Rec) -> Rec {
        self.into_rec() + rhs
    }
}

impl BitOr<Rec> for RangeInclusive<char> {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Rec {
        self.into_rec() | rhs
    }
}

impl PartialEq<Rec> for RangeInclusive<char> {
    fn eq(&self, other: &Rec) -> bool {
        self.clone().into_rec() == *other
    }
}

impl Element for RangeInclusive<char> {
    /// # Examples
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// assert_eq!('a'..='c', Rec::from(r"[a-c]"));
    /// ```
    fn into_rec(self) -> Rec {
        format!("[{}-{}]", self.start(), self.end()).into_rec()
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    #[inline]
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// let a_rec = "abc" + "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, Rec::from("abcxyz"));
    /// ```
    fn add(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}{}", self.into_rec(), rhs))
    }
}

impl BitOr<Rec> for &'_ str {
    type Output = Rec;

    /// ```
    /// use rec::{Element, Rec};
    ///
    /// let a_rec = "abc" | "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, Rec::from("abc|xyz"));
    /// ```
    fn bitor(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}|{}", self.into_rec(), rhs))
    }
}

impl PartialEq<Rec> for String {
    fn eq(&self, other: &Rec) -> bool {
        self.clone().into_rec() == *other
    }
}

impl Element for String {
    #[inline]
    fn into_rec(self) -> Rec {
        Rec(self)
    }
}

impl Add<Rec> for String {
    type Output = Rec;

    /// ```
    /// use rec::{Element, Rec};
    ///
    /// let a_rec = String::from("abc") + "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, Rec::from("abcxyz"));
    /// ```
    fn add(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}{}", self.into_rec(), rhs))
    }
}

impl BitOr<Rec> for String {
    type Output = Rec;

    /// ```
    /// use rec::{Element, Rec};
    ///
    /// let a_rec = String::from("abc") | "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, Rec::from("abc|xyz"));
    /// ```
    fn bitor(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}|{}", self.into_rec(), rhs))
    }
}

/// Constructs a regular expression.
///
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

    /// Ensures `self` is interpreted as one element.
    ///
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// assert_eq!(Rec::from("[[:alpha:]01]").group(), Rec::from("[[:alpha:]01]"));
    /// ```
    ///
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// assert_eq!(Rec::from(r"[a]\]").group(), Rec::from(r"(?:[a]\])"));
    /// ```
    ///
    /// ```
    /// use rec::{Element, Rec};
    ///
    /// assert_eq!(Rec::from("[ab][bc]").group(), Rec::from("(?:[ab][bc])"));
    /// ```
    fn group(self) -> Self {
        // Cannot use Rec to construct SINGLE_ELEMENT as that would call group() and cause infinite
        // recursion.
        lazy_static! {
            static ref SINGLE_ELEMENT: Pattern =
                Pattern::new(String::from(r"^(?:.?|(?:\[(?:[^\[]+|\[.*\])*[^\\]\]))$"));
        }

        if SINGLE_ELEMENT.is_match(&self.to_string()) {
            self
        } else {
            Self(format!("(?:{})", self))
        }
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
        Self(format!("{}{}", self, rhs.into_rec()))
    }
}

impl<T: Element> BitOr<T> for Rec {
    type Output = Self;

    #[inline]
    /// Sets lhs and rhs as possible alternatives.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!("a" + (Ch::Digit | ("b" + Ch::Whitespace)) + "c", Rec::from(r"a(?:\d|b\s)c"));
    /// ```
    fn bitor(self, rhs: T) -> Self {
        let new = Self(format!("{}|{}", self.0, rhs.into_rec()));
        new.group()
    }
}

impl Display for Rec {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Element for Rec {
    #[inline]
    fn into_rec(self) -> Self {
        self
    }
}

impl From<&str> for Rec {
    fn from(other: &str) -> Self {
        String::from(other).into_rec()
    }
}
