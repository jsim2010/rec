//! Implements character classes.
use crate::base::{Element, Rec};
use std::{fmt::{self, Display, Formatter}, ops::{Add, BitOr, Not}};

impl Add<Ch> for &str {
    type Output = Rec;

    #[inline]
    /// Adds `&str` and [`Ch`].
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!("hello" + Ch::Digit, String::from(r"hello\d").into_rec());
    /// ```
    fn add(self, rhs: Ch) -> Rec {
        self.into_rec() + rhs.into_rec()
    }
}

/// Defines all possible options for a single character.
#[derive(Clone, Copy, Debug)]
pub enum Ch {
    /// Matches a single specific character.
    Char(char),
    /// Matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Alpha.into_rec(), String::from("[[:alpha:]]").into_rec());
    /// ```
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::AlphaNum.into_rec(), String::from("[[:alnum:]]").into_rec());
    /// ```
    AlphaNum,
    /// Matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Digit.into_rec(), String::from(r"\d").into_rec());
    /// ```
    Digit,
    /// Matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Whitespace.into_rec(), String::from(r"\s").into_rec());
    /// ```
    Whitespace,
    /// Matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Any.into_rec(), String::from(".").into_rec());
    /// ```
    Any,
    /// Matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Start.into_rec(), String::from("^").into_rec());
    /// ```
    Start,
    /// Matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::End.into_rec(), String::from("$").into_rec());
    /// ```
    End,
    /// Matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::Sign.into_rec(), String::from(r"[+\-]").into_rec());
    /// ```
    Sign,
    /// Matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::NonZeroDigit.into_rec(), String::from(r"[1-9]").into_rec());
    /// ```
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::HexDigit.into_rec(), String::from("[[:xdigit:]]").into_rec());
    /// ```
    HexDigit,
}

impl Display for Ch {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", match self {
            Ch::Any => String::from("."),
            Ch::Digit => String::from(r"\d"),
            Ch::Whitespace => String::from(r"\s"),
            Ch::Start => String::from("^"),
            Ch::End => String::from("$"),
            Ch::Char(c) => match c {
                '-' => String::from(r"\-"),
                _ => c.to_string(),
            }
            Ch::Alpha => String::from("[:alpha:]"),
            Ch::AlphaNum => String::from("[:alnum:]"),
            Ch::Sign => String::from(r"[+\-]"),
            Ch::NonZeroDigit => String::from("[1-9]"),
            Ch::HexDigit => String::from("[:xdigit:]"),
        })
    }
}

impl PartialEq<Rec> for Ch {
    fn eq(&self, other: &Rec) -> bool {
        self.clone().into_rec() == *other
    }
}

impl Element for Ch {
    fn into_rec(self) -> Rec {
        let s = self.to_string();

        match self {
            Ch::Alpha | Ch::AlphaNum | Ch::HexDigit => format!("[{}]", s),
            _ => s,
        }.into_rec()
    }
}

#[derive(Clone, Debug)]
enum Operation {
    Identity,
    Range,
    Union,
}

/// Represents a match of one character.
#[derive(Clone, Debug)]
pub struct Class {
    chs: Vec<Ch>,
    op: Operation,
}

impl Class {
    const fn new(chs: Vec<Ch>, op: Operation) -> Self {
        Self {
            chs,
            op,
        }
    }

    fn identity(ch: Ch) -> Self {
        Self::new(vec![ch], Operation::Identity)
    }

    /// Creates a `Class` that matches with any of the given characters.
    ///
    /// # Examples
    /// ```
    /// use rec::{Class, Element};
    ///
    /// assert_eq!(Class::either("abc").into_rec(), String::from("[abc]").into_rec());
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::{Class, Element};
    ///
    /// assert_eq!(Class::either("a-c").into_rec(), String::from(r"[a\-c]").into_rec());
    /// ```
    pub fn either(chars: &str) -> Self {
        Self::union(chars.chars().map(Ch::Char).collect())
    }

    const fn union(chs: Vec<Ch>) -> Self {
        Self::new(chs, Operation::Union)
    }
}

impl<Rhs: Element> Add<Rhs> for Class {
    type Output = Rec;

    fn add(self, rhs: Rhs) -> Rec {
        self.into_rec() + rhs.into_rec()
    }
}

impl BitOr<Class> for Class {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match self.op {
            Operation::Union => {
                let mut output = self;
                output.chs.extend_from_slice(&rhs.chs);
                output
            }
            _ => Self::identity(Ch::Any),
        }
    }
}

impl BitOr<Rec> for Class {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.into_rec() | rhs
    }
}

impl PartialEq<Rec> for Class {
    fn eq(&self, other: &Rec) -> bool {
        dbg!(self.clone().into_rec());
        self.clone().into_rec() == *other
    }
}

impl Element for Class {
    fn into_rec(self) -> Rec {
        match self.op {
            Operation::Identity => {
                self.chs.first().map_or(Rec::from(""), |ch| ch.clone().into_rec())
            }
            Operation::Union => {
                let mut union = String::new();

                for ch in self.chs {
                    union.push_str(&ch.to_string());
                }

                format!("[{}]", union).into_rec()
            },
            _ => Rec::from("")
        }
    }
}

impl<Rhs: Element> Add<Rhs> for Ch {
    type Output = Rec;

    #[inline]
    fn add(self, rhs: Rhs) -> Rec {
        self.into_rec() + rhs.into_rec()
    }
}

impl BitOr<Rec> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.into_rec() | rhs
    }
}

impl BitOr<&str> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: &str) -> Self::Output {
        self.into_rec() | rhs.into_rec()
    }
}

/// ```
/// use rec::{Class, Element, Rec};
///
/// assert_eq!(Class::either("ab") | Class::either("cd"), Rec::from("[abcd]"));
/// ```
///
/// ```
/// use rec::{Ch, Element, Rec};
///
/// assert_eq!(Ch::Alpha | Ch::Whitespace, Rec::from(r"[[:alpha:]\s]"));
/// ```
///
/// ```
/// use rec::{Ch, Element, Rec};
///
/// assert_eq!(Ch::Alpha | Ch::Digit, Rec::from("[[:alnum:]]"));
/// ```
///
/// ```
/// use rec::{Ch, Element, Rec};
///
/// assert_eq!(Ch::Alpha | '0', Rec::from("[[:alpha:]0]"));
/// ```
///
/// Make sure alternation with multiple characters is not combined into 1 union.
/// ```
/// use rec::{Ch, Element, Rec};
///
/// assert_eq!(Ch::Alpha | "12", Rec::from("(?:[[:alpha:]]|12)"));
impl BitOr<Ch> for Ch {
    type Output = Class;

    fn bitor(self, rhs: Self) -> Self::Output {
        if let Ch::Alpha = self {
            if let Ch::Digit = rhs {
                return Class::identity(Ch::AlphaNum);
            }
        } else if let Ch::Digit = self {
            if let Ch::Alpha = rhs {
                return Class::identity(Ch::AlphaNum);
            }
        }

        Class::union(vec![self, rhs])
    }
}

impl BitOr<char> for Ch {
    type Output = Class;

    fn bitor(self, rhs: char) -> Self::Output {
        Class::union(vec![self, Ch::Char(rhs)])
    }
}

impl Not for Class {
    type Output = Self;

    // TODO: Fix this
    fn not(self) -> Self::Output {
        self
    }
}
