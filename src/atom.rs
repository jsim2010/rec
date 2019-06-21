//! Implements character classes.
use crate::base::{Element, Rec};
use std::{
    ops::{Add, BitOr},
    rc::Rc,
};

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

impl Element for char {
    fn to_regex(&self) -> String {
        self.to_string()
    }
}

/// An enumeration of predefined single character matches.
#[derive(Clone, Copy, Debug)]
pub enum Class {
    /// Matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Alpha, Rec::from("[[:alpha:]]"));
    /// ```
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::AlphaNum, Rec::from("[[:alnum:]]"));
    /// ```
    AlphaNum,
    /// Matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Digit, Rec::from(r"\d"));
    /// ```
    Digit,
    /// Matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Whitespace, Rec::from(r"\s"));
    /// ```
    Whitespace,
    /// Matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Any, Rec::from("."));
    /// ```
    Any,
    /// Matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Start, Rec::from("^"));
    /// ```
    Start,
    /// Matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::End, Rec::from("$"));
    /// ```
    End,
    /// Matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::Sign, Rec::from(r"[+\-]"));
    /// ```
    Sign,
    /// Matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::NonZeroDigit, Rec::from(r"[1-9]"));
    /// ```
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Class, Rec};
    ///
    /// assert_eq!(Class::HexDigit, Rec::from("[[:xdigit:]]"));
    /// ```
    HexDigit,
}

impl<Rhs: Element> Add<Rhs> for Class {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Rec {
        self.append(&rhs)
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
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!(Class::Alpha | '0', Rec::from("[[:alpha:]0]"));
    /// ```
    fn bitor(self, rhs: char) -> Self::Output {
        Ch::union(vec![Rc::new(self), Rc::new(rhs)])
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
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!(Class::Alpha | Class::Whitespace, Rec::from(r"[[:alpha:]\s]"));
    /// ```
    ///
    /// ```
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!(Class::Alpha | Class::Digit, Rec::from("[[:alnum:]]"));
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output {
        if let Class::Alpha = self {
            if let Class::Digit = rhs {
                return Ch::identity(Class::AlphaNum);
            }
        } else if let Class::Digit = self {
            if let Class::Alpha = rhs {
                return Ch::identity(Class::AlphaNum);
            }
        }

        Ch::union(vec![Rc::new(self), Rc::new(rhs)])
    }
}

// See BitOr<Class> for Class for more info.
impl BitOr<&str> for Class {
    type Output = Rec;

    /// ```
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!(Class::Alpha | "12", Rec::from("(?:[[:alpha:]]|12)"));
    /// ```
    fn bitor(self, rhs: &str) -> Self::Output {
        self.alternate(&rhs)
    }
}

// See BitOr<Class> for Class for more info.
impl BitOr<Rec> for Class {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.to_regex() | rhs
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
}

impl<T: Element> PartialEq<T> for Class {
    fn eq(&self, other: &T) -> bool {
        self.to_regex() == other.to_regex()
    }
}

// Required because cannot implement Add<T: Element> for &str.
impl Add<Class> for &str {
    type Output = Rec;

    #[inline]
    /// ```
    /// use rec::{Class, Element, Rec};
    ///
    /// assert_eq!("hello" + Class::Digit, Rec::from(r"hello\d"));
    /// ```
    fn add(self, rhs: Class) -> Rec {
        self.append(&rhs)
    }
}

/// Represents a match of one character.
///
/// A `Ch` is composed of [`Atom`]s combined with an [`Operation`]. Since `Ch`s implement
/// [`Atom`]s, this can expand recursively until a `Ch` with [`Operation::Identity`] is reached.
#[derive(Clone, Debug)]
pub struct Ch {
    atoms: Vec<Rc<dyn Atom>>,
    op: Operation,
}

impl Ch {
    fn new(atoms: Vec<Rc<dyn Atom>>, op: Operation) -> Self {
        Self { atoms, op }
    }

    fn identity(ch: Class) -> Self {
        Self::new(vec![Rc::new(ch)], Operation::Identity)
    }

    /// Creates a `Ch` that matches with any of the given characters.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!(Ch::either("abc"), Rec::from("[abc]"));
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!(Ch::either("a-c"), Rec::from(r"[a\-c]"));
    /// ```
    pub fn either(chars: &str) -> Self {
        let mut v: Vec<Rc<dyn Atom>> = Vec::new();

        for c in chars.chars() {
            v.push(Rc::new(c));
        }

        Self::union(v)
    }

    fn union(atoms: Vec<Rc<dyn Atom>>) -> Self {
        Self::new(atoms, Operation::Union)
    }

    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!(Ch::range('a', 'c'), Rec::from("[a-c]"));
    /// ```
    pub fn range(start: char, end: char) -> Self {
        Self::new(vec![Rc::new(start), Rc::new(end)], Operation::Range)
    }
}

impl<Rhs: Element> Add<Rhs> for Ch {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Rec {
        self.append(&rhs)
    }
}

impl Atom for Ch {
    fn to_part(&self) -> String {
        match self.op {
            Operation::Identity => format!(
                "{}",
                self.atoms
                    .first()
                    .map_or(String::default(), |atom| atom.to_part())
            ),
            Operation::Union => {
                let mut union = String::new();

                for atom in &self.atoms {
                    union.push_str(&atom.to_part());
                }

                format!("{}", union)
            }
            Operation::Range => {
                self.atoms[0].to_part() + "-" + self.atoms[1].to_part().as_str()
            }
        }
    }
}

// Ch | Ch has some cases where an output of Rec would not be ideal since it could still be bitor'd
// with another Atom. As a result, BitOr<Ch> is defined here and BitOr<T> must be defined for T:
// Element.
impl BitOr<Ch> for Ch {
    type Output = Self;

    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!(Ch::either("ab") | Ch::either("cd"), Rec::from("[abcd]"));
    /// ```
    ///
    /// ```
    /// use rec::{Ch, Rec};
    ///
    /// assert_eq!(Ch::range('a', 'c') | Ch::either("xyz"), Rec::from("[a-cxyz]"));
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::union(vec![Rc::new(self), Rc::new(rhs)])
    }
}

// See BitOr<Ch> for Ch.
impl BitOr<Rec> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.to_regex() | rhs
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
            Operation::Identity => self.atoms.first().unwrap().to_regex(),
            Operation::Union | Operation::Range => format!("[{}]", self.to_part()),
        }
    }
}

impl<T: Element> PartialEq<T> for Ch {
    fn eq(&self, other: &T) -> bool {
        self.to_regex() == other.to_regex()
    }
}

impl Add<Ch> for &str {
    type Output = Rec;

    /// ```
    /// use rec::{Ch, Element, Rec};
    ///
    /// assert_eq!("25" + Ch::range('0', '5'), Rec::from("25[0-5]"));
    /// ```
    fn add(self, rhs: Ch) -> Self::Output {
        self.append(&rhs)
    }
}

#[derive(Clone, Debug)]
enum Operation {
    Identity,
    Range,
    Union,
}
