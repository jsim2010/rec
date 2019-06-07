//! Implements character classes.
use crate::base::{Element, Rec};
use std::ops::{Add, BitOr, Not};

/// Represents a character that can match one or more characters.
#[derive(Debug)]
pub struct Ch<'a> {
    /// The [`Char`] representing the character.
    c: Char<'a>,
    /// If `c` needs to be negated.
    is_negated: bool,
}

impl Ch<'_> {
    /// Creates a `Ch` with the given [`Char`].
    const fn with_char(c: Char<'_>) -> Ch<'_> {
        Ch {
            c,
            is_negated: false,
        }
    }

    /// Creates a `Ch` that matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::any().into_rec(), String::from(".").into_rec());
    /// ```
    pub const fn any() -> Ch<'static> {
        Ch::with_char(Char::Any)
    }

    /// Creates a `Ch` that matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::alpha().into_rec(), String::from("[[:alpha:]]").into_rec());
    /// ```
    pub const fn alpha() -> Ch<'static> {
        Ch::with_char(Char::Class(CharClass::Alpha))
    }

    /// Creates a `Ch` that matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::alphanum().into_rec(), String::from("[[:alnum:]]").into_rec());
    pub const fn alphanum() -> Ch<'static> {
        Ch::with_char(Char::Class(CharClass::AlphaNum))
    }

    /// Creates a `Ch` that matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::digit().into_rec(), String::from(r"\d").into_rec());
    /// ```
    pub const fn digit() -> Ch<'static> {
        Ch::with_char(Char::Digit)
    }

    /// Creates a `Ch` that matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::whitespace().into_rec(), String::from(r"\s").into_rec());
    /// ```
    pub const fn whitespace() -> Ch<'static> {
        Ch::with_char(Char::Whitespace)
    }

    /// Creates a `Ch` that matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::start().into_rec(), String::from("^").into_rec());
    /// ```
    pub const fn start() -> Ch<'static> {
        Ch::with_char(Char::Start)
    }

    /// Creates a `Ch` that matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::end().into_rec(), String::from("$").into_rec());
    /// ```
    pub const fn end() -> Ch<'static> {
        Ch::with_char(Char::End)
    }

    /// Creates a `Ch` that matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::sign().into_rec(), String::from(r"[+\-]").into_rec());
    /// ```
    pub fn sign() -> Ch<'static> {
        Ch::union(r"+-")
    }

    /// Creates a `Ch` that matches with any of the given characters.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::union("abc").into_rec(), String::from("[abc]").into_rec());
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::union("a-c").into_rec(), String::from(r"[a\-c]").into_rec());
    /// ```
    pub fn union(chars: &str) -> Ch<'_> {
        Ch::with_char(Char::Union(chars))
    }
}

impl<Rhs: Element> Add<Rhs> for Ch<'_> {
    type Output = Rec;

    #[inline]
    fn add(self, rhs: Rhs) -> Rec {
        self.into_rec() + rhs
    }
}

impl<Rhs: Element> BitOr<Rhs> for Ch<'_> {
    type Output = Rec;

    #[inline]
    fn bitor(self, rhs: Rhs) -> Rec {
        self.into_rec() | rhs
    }
}

impl Element for Ch<'_> {
    fn into_rec(self) -> Rec {
        match self.c {
            Char::Any => String::from("."),
            Char::Digit => String::from(r"\d"),
            Char::Whitespace => String::from(r"\s"),
            Char::Start => String::from("^"),
            Char::End => String::from("$"),
            Char::Newline => String::from(r"\n"),
            Char::NotDigit => String::from(r"\D"),
            Char::NotWhitespace => String::from(r"\S"),
            Char::Union(chars) => {
                let chars = chars.replace("-", r"\-");

                if self.is_negated {
                    format!("[^{}]", chars)
                } else {
                    format!("[{}]", chars)
                }
            }
            Char::Class(class) => {
                let ch_class = class.id();

                if self.is_negated {
                    format!("[[:^{}:]]", ch_class)
                } else {
                    format!("[[:{}:]]", ch_class)
                }
            }
        }
        .into_rec()
    }
}

impl<'a> Not for Ch<'a> {
    type Output = Ch<'a>;

    fn not(self) -> Self::Output {
        let (c, is_negated) = match self.c {
            Char::Any => (Char::Newline, false),
            Char::Newline => (Char::Any, false),
            Char::Digit => (Char::NotDigit, false),
            Char::NotDigit => (Char::Digit, false),
            Char::Whitespace => (Char::NotWhitespace, false),
            Char::NotWhitespace => (Char::Whitespace, false),
            Char::End => (Char::Union("$"), true),
            Char::Start => (Char::Union("^"), true),
            Char::Union(_) | Char::Class(_) => (self.c, !self.is_negated),
        };
        Ch {
            c,
            is_negated,
        }
    }
}

/// Specifies one or more metacharacters to be matched against.
#[allow(variant_size_differences)] // Can't be resolved.
#[derive(Debug)]
enum Char<'a> {
    /// Matches any character except newline.
    Any,
    /// Matches any digit.
    Digit,
    /// Matches any whitespace.
    Whitespace,
    /// Matches the start of the text.
    Start,
    /// Matches the end of the text.
    End,
    /// Any of the given characters.
    Union(&'a str),
    /// The new line character.
    Newline,
    /// Matches any character that is not a digit.
    NotDigit,
    /// Matches any character that is not whitespace.
    NotWhitespace,
    Class(CharClass),
}

#[derive(Debug)]
enum CharClass {
    Alpha,
    AlphaNum,
}

impl CharClass {
    fn id(self) -> &'static str {
        match self {
            CharClass::Alpha => "alpha",
            CharClass::AlphaNum => "alnum",
        }
    }
}
