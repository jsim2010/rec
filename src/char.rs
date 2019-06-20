//! Implements character classes.
use crate::base::{Atom, Element, Rec};
use std::{
    ops::{Add, BitOr, Not, RangeInclusive},
    rc::Rc,
};

/// Defines all possible options for a single character.
#[derive(Clone, Copy, Debug)]
pub enum Ch {
    /// Matches any alphabetic character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Alpha, Rec::from("[[:alpha:]]"));
    /// ```
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::AlphaNum, Rec::from("[[:alnum:]]"));
    /// ```
    AlphaNum,
    /// Matches any numerical digit character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Digit, Rec::from(r"\d"));
    /// ```
    Digit,
    /// Matches any whitespace character.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Whitespace, Rec::from(r"\s"));
    /// ```
    Whitespace,
    /// Matches any character other than a newline.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Any, Rec::from("."));
    /// ```
    Any,
    /// Matches with the start of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Start, Rec::from("^"));
    /// ```
    Start,
    /// Matches with the end of the text.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::End, Rec::from("$"));
    /// ```
    End,
    /// Matches with the sign character of a number.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::Sign, Rec::from(r"[+\-]"));
    /// ```
    Sign,
    /// Matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::NonZeroDigit, Rec::from(r"[1-9]"));
    /// ```
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Atom, Ch, Rec};
    ///
    /// assert_eq!(Ch::HexDigit, Rec::from("[[:xdigit:]]"));
    /// ```
    HexDigit,
}

impl Atom for Ch {
    fn to_atom(&self) -> String {
        match self {
            Ch::Any => String::from("."),
            Ch::Digit => String::from(r"\d"),
            Ch::Whitespace => String::from(r"\s"),
            Ch::Start => String::from("^"),
            Ch::End => String::from("$"),
            Ch::Alpha => String::from("[:alpha:]"),
            Ch::AlphaNum => String::from("[:alnum:]"),
            Ch::Sign => String::from(r"[+\-]"),
            Ch::NonZeroDigit => String::from("[1-9]"),
            Ch::HexDigit => String::from("[:xdigit:]"),
        }
    }

    fn to_regex(&self) -> String {
        let atom = self.to_atom();

        match self {
            Ch::Alpha | Ch::AlphaNum | Ch::HexDigit => format!("[{}]", atom),
            _ => atom,
        }
    }
}

impl PartialEq<Rec> for Ch {
    fn eq(&self, other: &Rec) -> bool {
        self.to_rec() == *other
    }
}

#[derive(Clone, Debug)]
enum Operation {
    Identity,
    Range,
    Union,
}

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
        self.into_rec() + rhs.to_rec()
    }
}

/// Represents a match of one character.
#[derive(Clone, Debug)]
pub struct Class {
    atoms: Vec<Rc<dyn Atom>>,
    op: Operation,
}

impl Class {
    fn new(atoms: Vec<Rc<dyn Atom>>, op: Operation) -> Self {
        Self { atoms, op }
    }

    fn identity(ch: Ch) -> Self {
        Self::new(vec![Rc::new(ch)], Operation::Identity)
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
        let mut v: Vec<Rc<dyn Atom>> = Vec::new();

        for c in chars.chars() {
            v.push(Rc::new(c));
        }

        Self::union(v)
    }

    fn union(atoms: Vec<Rc<dyn Atom>>) -> Self {
        Self::new(atoms, Operation::Union)
    }
}

impl Atom for Class {
    fn to_atom(&self) -> String {
        match self.op {
            Operation::Identity => format!(
                "{}",
                self.atoms
                    .first()
                    .map_or(String::default(), |atom| atom.to_atom())
            ),
            Operation::Union => {
                let mut union = String::new();

                for atom in &self.atoms {
                    union.push_str(&atom.to_atom());
                }

                format!("{}", union)
            }
            Operation::Range => {
                let (first, rest) = self
                    .atoms
                    .split_first()
                    .map(|(f, r)| (f.to_atom(), r))
                    .unwrap();
                format!(
                    "{}-{}",
                    first,
                    rest.first()
                        .map_or(String::default(), |atom| atom.to_atom())
                )
            }
        }
    }

    fn to_regex(&self) -> String {
        match self.op {
            Operation::Identity => self.to_atom(),
            Operation::Union => format!("[{}]", self.to_atom()),
            _ => String::default(),
        }
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
        Self::union(vec![Rc::new(self), Rc::new(rhs)])
    }
}

impl From<RangeInclusive<char>> for Class {
    fn from(other: RangeInclusive<char>) -> Self {
        Self::new(
            vec![
                Rc::new(*other.start()),
                Rc::new(*other.end()),
            ],
            Operation::Range,
        )
    }
}

impl BitOr<Class> for RangeInclusive<char> {
    type Output = Class;

    /// ```
    /// use rec::{Class, Rec};
    ///
    /// assert_eq!(('a'..='c') | Class::either("xyz"), Rec::from("[a-cxyz]"));
    /// ```
    fn bitor(self, rhs: Class) -> Self::Output {
        Class::from(self) | rhs
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
            Operation::Identity => self.atoms.first().unwrap().to_rec(),
            Operation::Union => format!("[{}]", self.to_atom()).into_rec(),
            _ => Rec::from(""),
        }
    }

    fn group(self) -> Rec {
        self.into_rec()
    }
}

impl<Rhs: Element> Add<Rhs> for Ch {
    type Output = Rec;

    #[inline]
    fn add(self, rhs: Rhs) -> Rec {
        self.to_rec() + rhs.into_rec()
    }
}

impl BitOr<Rec> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Self::Output {
        self.to_rec() | rhs
    }
}

impl BitOr<&str> for Ch {
    type Output = Rec;

    fn bitor(self, rhs: &str) -> Self::Output {
        self.to_rec() | rhs.into_rec()
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

        Class::union(vec![Rc::new(self), Rc::new(rhs)])
    }
}

impl BitOr<char> for Ch {
    type Output = Class;

    fn bitor(self, rhs: char) -> Self::Output {
        Class::union(vec![Rc::new(self), Rc::new(rhs)])
    }
}

impl Not for Class {
    type Output = Self;

    // TODO: Fix this
    fn not(self) -> Self::Output {
        self
    }
}
