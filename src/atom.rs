//! Implements character classes.
use crate::prelude::*;
use core::ops::{Add, BitOr};

/// An enumeration of predefined single character matches.
#[derive(Clone, Copy, Debug)]
pub enum Class {
    /// Matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha, Rec::from("[[:alpha:]]"));
    /// ```
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::AlphaNum, Rec::from("[[:alnum:]]"));
    /// ```
    AlphaNum,
    /// Matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Digit, Rec::from(r"\d"));
    /// ```
    Digit,
    /// Matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Whitespace, Rec::from(r"\s"));
    /// ```
    Whitespace,
    /// Matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Any, Rec::from("."));
    /// ```
    Any,
    /// Matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Start, Rec::from("^"));
    /// ```
    Start,
    /// Matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::End, Rec::from("$"));
    /// ```
    End,
    /// Matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Sign, Rec::from(r"[+\-]"));
    /// ```
    Sign,
    /// Matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::NonZeroDigit, Rec::from(r"[1-9]"));
    /// ```
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::HexDigit, Rec::from("[[:xdigit:]]"));
    /// ```
    HexDigit,
}

impl<Rhs: Element> Add<Rhs> for Class {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl Atom for Class {
    fn to_part(&self) -> String {
        match self {
            Class::Any => String::from("."),
            Class::Digit => String::from(r"\d"),
            Class::Whitespace => String::from(r"\s"),
            Class::Start => String::from("^"),
            Class::End => String::from("$"),
            Class::Alpha => String::from("[:alpha:]"),
            Class::AlphaNum => String::from("[:alnum:]"),
            Class::Sign => String::from(r"+\-"),
            Class::NonZeroDigit => String::from("1-9"),
            Class::HexDigit => String::from("[:xdigit:]"),
        }
    }
}

impl BitOr<char> for Class {
    type Output = Ch;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha | '0', Rec::from("[[:alpha:]0]"));
    /// ```
    fn bitor(self, rhs: char) -> Self::Output {
        Ch::Union(vec![self.to_part(), rhs.to_part()])
    }
}

// Class | Class has some cases where an output of Rec would not be ideal since it could still be
// bitor'd with another Atom. As a result, BitOr<Class> is defined here and BitOr<T> must be
// defined for T: Element.
impl BitOr<Class> for Class {
    // Although there are some cases where outputing a Class would be ideal, in the case of a union
    // of 2 classes, we must output a Ch.
    type Output = Ch;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha | Class::Whitespace, Rec::from(r"[[:alpha:]\s]"));
    /// ```
    ///
    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha | Class::Digit, Rec::from("[[:alnum:]]"));
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output {
        if let Class::Alpha = self {
            if let Class::Digit = rhs {
                return Ch::Union(vec![Class::AlphaNum.to_part()]);
            }
        } else if let Class::Digit = self {
            if let Class::Alpha = rhs {
                return Ch::Union(vec![Class::AlphaNum.to_part()]);
            }
        }

        Ch::Union(vec![self.to_part(), rhs.to_part()])
    }
}

impl BitOr<&str> for Class {
    type Output = Rec;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha | "12", Rec::from("[[:alpha:]]|12"));
    /// ```
    fn bitor(self, rhs: &str) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl BitOr<Rec> for Class {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl Element for Class {
    fn to_regex(&self) -> String {
        let part = self.to_part();

        match self {
            Class::Alpha
            | Class::AlphaNum
            | Class::HexDigit
            | Class::Sign
            | Class::NonZeroDigit => format!("[{}]", part),
            _ => part,
        }
    }

    fn is_atom(&self) -> bool {
        true
    }
}

impl<T: Element> PartialEq<T> for Class {
    fn eq(&self, other: &T) -> bool {
        self.is_equal(other)
    }
}

/// Represents a match of one character.
#[derive(Debug)]
pub enum Ch {
    /// Matches any of the chars in the given &str.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::AnyOf("abc"), Rec::from("[abc]"));
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::AnyOf("a-c"), Rec::from(r"[a\-c]"));
    /// ```
    AnyOf(&'static str),
    /// Matches any of the given parts.
    Union(Vec<String>),
    /// Matches any character between (inclusive) the 2 given chars.
    Range(char, char),
}

impl<Rhs: Element> Add<Rhs> for Ch {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl Atom for Ch {
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::Range('a', 'c'), Rec::from("[a-c]"));
    /// ```
    fn to_part(&self) -> String {
        match self {
            Ch::AnyOf(chars) => chars.replace('-', r"\-"),
            Ch::Union(parts) => {
                let mut union = String::new();

                for atom in parts {
                    union.push_str(atom);
                }

                union
            }
            Ch::Range(start, end) => format!("{}-{}", start, end),
        }
    }
}

// Ch | Ch has some cases where an output of Rec would not be ideal since it could still be bitor'd
// with another Atom. As a result, BitOr<Ch> is defined here and BitOr<T> must be defined for T:
// Element.
impl BitOr for Ch {
    type Output = Self;

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::AnyOf("ab") | Ch::AnyOf("cd"), Rec::from("[abcd]"));
    /// ```
    ///
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::Range('a', 'c') | Ch::AnyOf("xyz"), Rec::from("[a-cxyz]"));
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output {
        Ch::Union(vec![self.to_part(), rhs.to_part()])
    }
}

impl BitOr<char> for Ch {
    type Output = Self;

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::AnyOf("ab") | 'c', Rec::from("[abc]"));
    /// ```
    fn bitor(self, rhs: char) -> Self::Output {
        Ch::Union(vec![self.to_part(), rhs.to_part()])
    }
}

impl BitOr<Rec> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl BitOr<&str> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: &str) -> Self::Output {
        self.alternate(&rhs)
    }
}

impl Element for Ch {
    fn to_regex(&self) -> String {
        format!("[{}]", self.to_part())
    }

    fn is_atom(&self) -> bool {
        true
    }
}

impl<T: Element> PartialEq<T> for Ch {
    fn eq(&self, other: &T) -> bool {
        self.is_equal(other)
    }
}

impl Add<Ch> for char {
    type Output = Rec;

    fn add(self, rhs: Ch) -> Self::Output {
        self.concatenate(&rhs)
    }
}

// Required because cannot implement Add<T: Element> for char.
impl Add<Class> for char {
    type Output = Rec;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!('a' + Class::Digit, Rec::from(r"a\d"));
    /// ```
    fn add(self, rhs: Class) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl BitOr<Ch> for Rec {
    type Output = Self;

    fn bitor(self, rhs: Ch) -> Self::Output {
        let mut elements = self.elements;
        elements.push(rhs.to_regex());
        Self::alternation(elements)
    }
}

impl Add<Ch> for &str {
    type Output = Rec;

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!("25" + Ch::Range('0', '5'), Rec::from("25[0-5]"));
    /// ```
    fn add(self, rhs: Ch) -> Self::Output {
        self.concatenate(&rhs)
    }
}

// Required because cannot implement Add<T: Element> for &str.
impl Add<Class> for &str {
    type Output = Rec;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!("hello" + Class::Digit, Rec::from(r"hello\d"));
    /// ```
    fn add(self, rhs: Class) -> Self::Output {
        self.concatenate(&rhs)
    }
}
