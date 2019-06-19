//! Implements base items used throughout `rec`.
use crate::Pattern;
use lazy_static::lazy_static;
use regex::Regex;
use std::fmt::{self, Display, Formatter};
use std::ops::{Add, BitOr};

/// Signifies elements that can be converted into a [`Rec`].
pub trait Element: Add<Rec> + BitOr<Rec> {
    /// Converts `self` into a [`Rec`].
    fn into_rec(self) -> Rec;

    /// Converts `self` into a [`Rec`] that is grouped.
    fn group(self) -> Rec
    where
        Self: Sized,
    {
        self.into_rec().group()
    }

    /// Returns the representation of `self` as part of a [`Char::Union`], if it exists.
    fn unionable_value(&self) -> Option<String> {
        None
    }
}

impl Element for &str {
    #[inline]
    /// ```
    /// use rec::Element;
    ///
    /// assert_eq!(".+*?|[]".into_rec(), String::from(r"\.\+\*\?\|\[\]").into_rec());
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

    fn unionable_value(&self) -> Option<String> {
        if self.len() == 1 {
            Some(String::from(*self))
        } else {
            None
        }
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    #[inline]
    /// ```
    /// use rec::Element;
    ///
    /// let a_rec = "abc" + "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, String::from("abcxyz").into_rec());
    /// ```
    fn add(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}{}", self.into_rec(), rhs))
    }
}

impl BitOr<Rec> for &'_ str {
    type Output = Rec;

    /// ```
    /// use rec::Element;
    ///
    /// let a_rec = "abc" | "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, String::from("abc|xyz").into_rec());
    /// ```
    fn bitor(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}|{}", self.into_rec(), rhs))
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
    /// use rec::Element;
    ///
    /// let a_rec = String::from("abc") + "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, String::from("abcxyz").into_rec());
    /// ```
    fn add(self, rhs: Rec) -> Self::Output {
        Rec(format!("{}{}", self.into_rec(), rhs))
    }
}

impl BitOr<Rec> for String {
    type Output = Rec;

    /// ```
    /// use rec::Element;
    ///
    /// let a_rec = String::from("abc") | "xyz".into_rec();
    ///
    /// assert_eq!(a_rec, String::from("abc|xyz").into_rec());
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
    /// use rec::Element;
    ///
    /// assert_eq!(String::from("[[:alpha:]01]").into_rec().group(), String::from("[[:alpha:]01]").into_rec());
    /// ```
    ///
    /// ```
    /// use rec::Element;
    ///
    /// assert_eq!(String::from(r"[a]\]").into_rec().group(), String::from(r"(?:[a]\])").into_rec());
    /// ```
    ///
    /// ```
    /// use rec::Element;
    ///
    /// assert_eq!(String::from("[ab][bc]").into_rec().group(),
    /// String::from("(?:[ab][bc])").into_rec());
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
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!("a" + (Ch::digit() | ("b" + Ch::whitespace())) + "c", String::from(r"a(?:\d|b\s)c").into_rec());
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
