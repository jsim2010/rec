//! Implements character classes.
use core::ops::{Add, BitOr};
use crate::prelude::*;

/// An entity that attempts to match with a single character of the searched text.
///
/// A [`char`] represents an `Atom`.
pub trait Atom: Element {
    /// Converts `self` to a [`String`] that contains everything inside the `[]` brackets.
    fn to_part(&self) -> String;
}

impl Atom for char {
    fn to_part(&self) -> String {
        match self {
            '-' => String::from(r"\-"),
            _ => self.to_string(),
        }
    }
}

/// An enumeration of predefined single character matches.
#[derive(Clone, Copy, Debug)]
pub enum Class {
    /// Matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha, Rec::from("[[:alpha:]]"));
    /// ```
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::AlphaNum, Rec::from("[[:alnum:]]"));
    /// ```
    AlphaNum,
    /// Matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Digit, Rec::from(r"\d"));
    /// ```
    Digit,
    /// Matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Whitespace, Rec::from(r"\s"));
    /// ```
    Whitespace,
    /// Matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Any, Rec::from("."));
    /// ```
    Any,
    /// Matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Start, Rec::from("^"));
    /// ```
    Start,
    /// Matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::End, Rec::from("$"));
    /// ```
    End,
    /// Matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::Sign, Rec::from(r"[+\-]"));
    /// ```
    Sign,
    /// Matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
    ///
    /// assert_eq!(Class::NonZeroDigit, Rec::from(r"[1-9]"));
    /// ```
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, prelude::*};
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
            Class::Sign => String::from(r"[+\-]"),
            Class::NonZeroDigit => String::from("[1-9]"),
            Class::HexDigit => String::from("[:xdigit:]"),
        }
    }
}

// See BitOr<Class> for Class for more info.
impl BitOr<char> for Class {
    type Output = Ch;

    /// ```
    /// use rec::{Class, prelude::*};
    ///
    /// assert_eq!(Class::Alpha | '0', Rec::from("[[:alpha:]0]"));
    /// ```
    fn bitor(self, rhs: char) -> Self::Output {
        Ch::union(vec![self.to_part(), rhs.to_part()])
    }
}

// Class | Class has some cases where an output of Rec would not be ideal since it could still be
// bitor'd with another Atom. As a result, BitOr<Class> is defined here and BitOr<T> must be
// defined for T: Element.
impl BitOr<Class> for Class {
    // Although there are some cases where outputing a Class would be ideal, in the case of a union
    // of 2 classes, we must output a Ch. We account for the cases that would output a Class by
    // outputing a Ch with Operation::Identity.
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
                return Ch::ascii(Class::AlphaNum);
            }
        } else if let Class::Digit = self {
            if let Class::Alpha = rhs {
                return Ch::ascii(Class::AlphaNum);
            }
        }

        Ch::union(vec![self.to_part(), rhs.to_part()])
    }
}

// See BitOr<Class> for Class for more info.
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

// See BitOr<Class> for Class for more info.
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
            Class::Alpha | Class::AlphaNum | Class::HexDigit => format!("[{}]", part),
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

/// Represents a match of one character.
///
/// A `Ch` is composed of [`String`]s (AKA parts) combined with an [`Operation`].
#[derive(Clone, Debug)]
pub struct Ch {
    parts: Vec<String>,
    op: Operation,
}

impl Ch {
    const fn new(parts: Vec<String>, op: Operation) -> Self {
        Self { parts, op }
    }

    fn ascii(class: Class) -> Self {
        Self::new(vec![class.to_part()], Operation::Ascii)
    }

    /// Creates a `Ch` that matches with any of the given characters.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::either("abc"), Rec::from("[abc]"));
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::either("a-c"), Rec::from(r"[a\-c]"));
    /// ```
    pub fn either(chars: &str) -> Self {
        let mut parts: Vec<String> = Vec::new();

        for c in chars.chars() {
            parts.push(c.to_part());
        }

        Self::union(parts)
    }

    const fn union(parts: Vec<String>) -> Self {
        Self::new(parts, Operation::Union)
    }

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::range('a', 'c'), Rec::from("[a-c]"));
    /// ```
    pub fn range(start: char, end: char) -> Self {
        Self::new(vec![start.to_part(), end.to_part()], Operation::Range)
    }
}

impl<Rhs: Element> Add<Rhs> for Ch {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Self::Output {
        self.concatenate(&rhs)
    }
}

impl Atom for Ch {
    fn to_part(&self) -> String {
        match self.op {
            Operation::Union => {
                let mut union = String::new();

                for atom in &self.parts {
                    union.push_str(atom);
                }

                union
            }
            Operation::Range => self.parts[0].clone() + "-" + self.parts[1].as_str(),
            Operation::Ascii => self.parts[0].clone(),
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
    /// assert_eq!(Ch::either("ab") | Ch::either("cd"), Rec::from("[abcd]"));
    /// ```
    ///
    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::range('a', 'c') | Ch::either("xyz"), Rec::from("[a-cxyz]"));
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::union(vec![self.to_part(), rhs.to_part()])
    }
}

// See BitOr<Ch> for Ch.
impl BitOr<char> for Ch {
    type Output = Self;

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!(Ch::either("ab") | 'c', Rec::from("[abc]"));
    /// ```
    fn bitor(self, rhs: char) -> Self::Output {
        Self::union(vec![self.to_part(), rhs.to_part()])
    }
}

// See BitOr<Ch> for Ch.
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
        match self.op {
            Operation::Union | Operation::Range | Operation::Ascii => {
                format!("[{}]", self.to_part())
            }
        }
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

impl Add<Ch> for &str {
    type Output = Rec;

    /// ```
    /// use rec::{Ch, prelude::*};
    ///
    /// assert_eq!("25" + Ch::range('0', '5'), Rec::from("25[0-5]"));
    /// ```
    fn add(self, rhs: Ch) -> Self::Output {
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

#[derive(Clone, Debug)]
enum Operation {
    Ascii,
    Range,
    Union,
}
