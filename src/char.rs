use crate::base::{Element, Rec};
use std::ops::{Add, BitOr, Not};

#[derive(Debug)]
pub struct Ch<'a> {
    c: Char<'a>,
    is_not: bool,
}

impl Ch<'_> {
    fn with_char(c: Char<'_>) -> Ch<'_> {
        Ch { c, is_not: false }
    }

    pub fn any() -> Ch<'static> {
        Ch::with_char(Char::Any)
    }

    pub fn digit() -> Ch<'static> {
        Ch::with_char(Char::Digit)
    }

    pub fn whitespace() -> Ch<'static> {
        Ch::with_char(Char::Whitespace)
    }

    pub fn end() -> Ch<'static> {
        Ch::with_char(Char::End)
    }

    pub fn sign() -> Ch<'static> {
        Ch::union(r"-+")
    }

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
            Char::End => String::from("$"),
            Char::Newline => String::from(r"\n"),
            Char::NotDigit => String::from(r"\D"),
            Char::NotWhitespace => String::from(r"\S"),
            Char::Union(chars) => {
                if self.is_not {
                    format!("[{}]", chars)
                } else {
                    format!("[^{}]", chars)
                }
            }
        }.into_rec()
    }
}

impl<'a> Not for Ch<'a> {
    type Output = Ch<'a>;

    fn not(self) -> Self::Output {
        let (c, is_not) = match self.c {
            Char::Any => (Char::Newline, false),
            Char::Newline => (Char::Any, false),
            Char::Digit => (Char::NotDigit, false),
            Char::NotDigit => (Char::Digit, false),
            Char::Whitespace => (Char::NotWhitespace, false),
            Char::NotWhitespace => (Char::Whitespace, false),
            Char::End => (Char::Union("$"), true),
            Char::Union(chars) => (Char::Union(chars), !self.is_not),
        };
        Ch { c, is_not }
    }
}

/// Specifies one or more metacharacters to be matched against.
#[derive(Debug)]
enum Char<'a> {
    /// Matches any character except newline.
    Any,
    /// Matches any digit.
    Digit,
    /// Matches any whitespace.
    Whitespace,
    /// Matches the end of the text.
    End,
    /// Any of the given characters.
    Union(&'a str),
    /// The new line character.
    Newline,
    NotDigit,
    NotWhitespace,
}
