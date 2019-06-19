//! Implements character classes.
use crate::base::{Element, Rec};
use std::ops::{Add, BitOr, Not};

impl Add<Ch<'_>> for &str {
    type Output = Rec;

    #[inline]
    /// Adds `&str` and [`Ch`].
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!("hello" + Ch::digit(), String::from(r"hello\d").into_rec());
    /// ```
    fn add(self, rhs: Ch<'_>) -> Rec {
        self.into_rec() + rhs
    }
}

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

    fn negate_sign(&self) -> String {
        if self.is_negated {
            String::from("^")
        } else {
            String::new()
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

    /// Creates a `Ch` that matches with any character between or including the given characters.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::range('a', 'c').into_rec(), String::from(r"[a-c]").into_rec());
    /// ```
    pub fn range(first: char, last: char) -> Ch<'static> {
        Ch::with_char(Char::Range(first, last))
    }

    /// Creates a `Ch` that matches with any digit that is not `0`.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::digitnz().into_rec(), String::from(r"[1-9]").into_rec());
    /// ```
    pub fn digitnz() -> Ch<'static> {
        Ch::with_char(Char::Range('1', '9'))
    }

    /// Creates a `Ch` that matches with any hexidecimal digit.
    ///
    /// # Examples
    /// ```
    /// use rec::{Ch, Element};
    ///
    /// assert_eq!(Ch::hexdigit().into_rec(), String::from("[[:xdigit:]]").into_rec());
    /// ```
    pub fn hexdigit() -> Ch<'static> {
        Ch::with_char(Char::Class(CharClass::HexDigit))
    }
}

impl<Rhs: Element> Add<Rhs> for Ch<'_> {
    type Output = Rec;

    #[inline]
    fn add(self, rhs: Rhs) -> Rec {
        self.into_rec() + rhs
    }
}

/// ```
/// use rec::{Ch, Element};
///
/// assert_eq!(Ch::union("ab") | Ch::union("c"), String::from("[abc]").into_rec());
/// ```
///
/// ```
/// use rec::{Ch, Element};
///
/// assert_eq!(Ch::alpha() | Ch::whitespace(), String::from(r"[[:alpha:]\s]").into_rec());
/// ```
///
/// ```
/// use rec::{Ch, Element};
///
/// assert_eq!(Ch::alpha() | Ch::digit(), String::from("[[:alnum:]]").into_rec());
/// ```
///
/// ```
/// use rec::{Ch, Element};
///
/// assert_eq!(Ch::alpha() | "0", String::from("[[:alpha:]0]").into_rec());
/// ```
///
/// Make sure alternation with multiple characters is not combined into 1 union.
/// ```
/// use rec::{Ch, Element};
///
/// assert_eq!(Ch::alpha() | "12", String::from("(?:[[:alpha:]]|12)").into_rec());
impl<Rhs: Element> BitOr<Rhs> for Ch<'_> {
    type Output = Rec;

    #[inline]
    fn bitor(self, rhs: Rhs) -> Rec {
        if let Some(l_value) = self.unionable_value() {
            if let Some(r_value) = rhs.unionable_value() {
                if (l_value == "[:alpha:]" && r_value == r"\d") || (l_value == r"\d" && r_value == "[[:alpha:]]") {
                    return Ch::alphanum().into_rec();
                }

                return format!("[{}{}]", l_value, r_value).into_rec();
            }
        }

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
            Char::Union(chars) => format!("[{}{}]", self.negate_sign(), chars.replace("-", r"\-")),
            Char::Class(class) => format!("[[:{}{}:]]", self.negate_sign(), class.id()),
            Char::Range(first, last) => format!("[{}{}-{}]", self.negate_sign(), first, last),
        }
        .into_rec()
    }

    fn unionable_value(&self) -> Option<String> {
        match self.c {
            Char::Union(chars) => Some(String::from(chars)),
            Char::Class(class) => Some(format!("[:{}:]", class.id())),
            Char::Whitespace => Some(String::from(r"\s")),
            Char::Digit => Some(String::from(r"\d")),
            _ => None,
        }
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
            Char::Union(_) | Char::Class(_) | Char::Range(_, _) => (self.c, !self.is_negated),
        };
        Ch { c, is_negated }
    }
}

/// Specifies one or more metacharacters to be matched against.
#[allow(variant_size_differences)] // Cannot be resolved.
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
    Range(char, char),
}

#[derive(Clone, Copy, Debug)]
enum CharClass {
    Alpha,
    AlphaNum,
    HexDigit,
}

impl CharClass {
    fn id(self) -> &'static str {
        match self {
            CharClass::Alpha => "alpha",
            CharClass::AlphaNum => "alnum",
            CharClass::HexDigit => "xdigit",
        }
    }
}
