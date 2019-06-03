//! Implements base items used throughout `rec`.
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
}

impl Element for &str {
    #[inline]
    /// ```
    /// use rec::Element;
    ///
    /// assert_eq!(".+*?|".into_rec(), String::from(r"\.\+\*\?\|").into_rec());
    /// ```
    fn into_rec(self) -> Rec {
        Rec(self
            .replace(".", r"\.")
            .replace("+", r"\+")
            .replace("*", r"\*")
            .replace("?", r"\?")
            .replace("|", r"\|"))
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

    /// Groups together all of `self`.
    fn group(self) -> Self {
        let length = self.0.chars().count();

        if length > 2 || (length == 2 && self.0.chars().nth(0) != Some('\\')) {
            return Self(format!("(?:{})", self));
        }

        self
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
