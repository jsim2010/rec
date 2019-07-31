//! Common items used by `rec`.
use alloc::{
    format,
    string::{String, ToString},
    vec,
    vec::{IntoIter, Vec},
};
use core::{
    fmt::{self, Debug, Display, Formatter},
    iter::{self, Chain, Once},
    ops::{Bound, Div, Mul, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeToInclusive},
};
use rec_derive::{AtomOps, ComponentOps};
use regex::Regex;

// Used to implement Repeater for every RangeBounds trait.
// Ideally, impl<T: RangeBounds<u128>> Repeater for T would work, however this is not allowed as
// impl Repeater for u128 is also needed and u128 could impl RangeBounds<u128> in the future.
macro_rules! impl_repeater_for_rangebounds {
    ($range:ty) => {
        impl Repeater for $range {
            fn start(&self) -> Bound<&u128> {
                self.start_bound()
            }

            fn end(&self) -> Bound<&u128> {
                self.end_bound()
            }
        }
    };
}

/// An item that can be converted into a regular expression.
pub trait Element {
    /// Converts `self` to a regular expression compatible with [`regex`].
    fn to_regex(&self) -> String;

    /// Returns if `self` is able to be interpreted as an [`Atom`].
    fn is_atom(&self) -> bool;

    /// Converts `self` to a regular expression that is grouped together.
    fn to_grouped_regex(&self) -> String {
        if self.is_atom() {
            // Atoms do not require explicit grouping.
            self.to_regex()
        } else {
            format!("(?:{})", self.to_regex())
        }
    }

    /// Converts `self` to a regular expression that is a member of a concatenation.
    ///
    /// [`Element`]s whose regular expression is not always chainable should override.
    fn to_chainable_regex(&self) -> String {
        self.to_regex()
    }

    /// Returns each possible match in `self`.
    ///
    /// [`Element`]s that may have multiple possible matches should override.
    fn possibilities(&self) -> Members {
        Members::with_one(self.to_regex())
    }

    /// Creates a [`Rec`] from the concatenation of `self` and `other`.
    ///
    /// Implements the functionality of [`Add`] for all [`Element`]s.
    fn concatenate(&self, other: &dyn Element) -> Rec {
        Rec::concatenation(
            iter::once(self.to_chainable_regex()).chain(iter::once(other.to_chainable_regex())),
        )
    }

    /// Creates a [`Rec`] from the alternation of `self` and `other`.
    ///
    /// Implements the functionality of [`BitOr`] for all [`Element`]s where at least one
    /// [`Element`] is a [`Component`].
    fn alternate(&self, other: &dyn Element) -> Rec {
        Rec::alternation(self.possibilities().chain(other.possibilities()))
    }

    /// Creates a [`Rec`] that repeats `self` as specified by `repeat`.
    ///
    /// Implements the functionality of [`Div`] and [`Mul`] for all [`Element`]s.
    fn repeat(&self, repeat: Repeat) -> Rec {
        Rec::from(format!("{}{}", self.to_grouped_regex(), repeat))
    }

    /// Returns if the regular expression of `self` is equal to that of `other`.
    ///
    /// Implements the functionality of [`PartialEq`] for all [`Element`]s.
    fn is_equal(&self, other: &dyn Element) -> bool {
        self.to_regex() == other.to_regex()
    }

    /// Attempts to build a [`Regex`] from `self`.
    ///
    /// This is intended to be used with [`Element`]s that are not known prior to runtime.
    /// Otherwise use [`build`].
    fn try_build(&self) -> Result<Regex, regex::Error> {
        Regex::new(&self.to_regex())
    }

    /// Builds a [`Regex`] from `self`.
    ///
    /// This is only safe to use with [`Element`]s that are known prior to runtime. Otherwise use
    /// [`try_build`].
    ///
    /// # Panics
    ///
    /// Panics if `self` converts to an invalid regular expression.
    #[allow(clippy::result_unwrap_used)] // Panic on error is intended.
    fn build(&self) -> Regex {
        self.try_build().unwrap()
    }
}

/// An [`Element`] that attempts to match with a single character of the input text.
pub trait Atom: Element {
    /// Converts `self` to its representation as a part of an `Atom`.
    ///
    /// The part representation must be valid within the `[]` bracket syntax of [`regex`].
    fn to_part(&self) -> String;

    /// Creates a [`Ch`] that matches any character described by either `self` or `other`.
    ///
    /// Implements the functionality of [`BitOr`] for all [`Atom`]s.
    fn union(&self, other: &dyn Atom) -> Ch {
        Ch::Union(vec![self.to_part(), other.to_part()])
    }
}

/// An [`Element`] that attempts to match with more than one character of the input text.
pub trait Compound: Element + Debug {}

/// An [`Iterator`] of regular expressions.
#[derive(Debug)]
pub enum Members {
    /// Iterates over a single regular expression.
    Single(Once<String>),
    /// Iterates over multiple regular expressions.
    Multiple(IntoIter<String>),
}

impl Members {
    fn with_one(member: String) -> Self {
        Members::Single(iter::once(member))
    }

    fn with_multiple(members: Vec<String>) -> Self {
        Members::Multiple(members.into_iter())
    }
}

impl Iterator for Members {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Members::Single(i) => i.next(),
            Members::Multiple(i) => i.next(),
        }
    }
}

/// Combines individual regular expressions into a single one.
#[derive(Debug, ComponentOps)]
pub struct Rec {
    /// The individual regular expressions.
    members: Vec<String>,
    /// How `members` are composed together.
    composition: Composition,
}

impl Rec {
    /// Creates a new [`Rec`] with `members` composed by [`Composition::Alternation`].
    fn alternation(members: Chain<Members, Members>) -> Self {
        Self {
            members: members.collect(),
            composition: Composition::Alternation,
        }
    }

    /// Creates a new [`Rec`] with `members` composed by [`Composition::Concatenation`].
    fn concatenation(members: impl Iterator<Item = String>) -> Self {
        Self {
            members: members.collect(),
            composition: Composition::Concatenation,
        }
    }
}

impl Compound for Rec {}

impl Element for Rec {
    fn to_regex(&self) -> String {
        let mut regex = String::new();
        let mut is_first = true;

        for element in &self.members {
            if is_first {
                is_first = false;
            } else {
                match self.composition {
                    Composition::Alternation => {
                        regex.push('|');
                    }
                    Composition::Concatenation => {}
                }
            }

            regex.push_str(element);
        }

        regex
    }

    fn is_atom(&self) -> bool {
        false
    }

    fn possibilities(&self) -> Members {
        match self.composition {
            Composition::Alternation => Members::with_multiple(self.members.clone()),
            Composition::Concatenation => Members::with_one(self.to_regex()),
        }
    }

    fn to_chainable_regex(&self) -> String {
        match self.composition {
            Composition::Concatenation => self.to_regex(),
            Composition::Alternation => self.to_grouped_regex(),
        }
    }
}

impl From<&str> for Rec {
    /// Converts a regular expression [`&str`] into a `Rec`.
    ///
    /// Intended use is for testing purposes, where the provided [`&str`] is is directly used to
    /// build the [`Regex`], i.e.: the metacharacters will not be escaped. If not using for tests,
    /// see [`Element::build`], ex: `"regex".build()"`.
    fn from(other: &str) -> Self {
        Self::from(other.to_string())
    }
}

impl From<String> for Rec {
    /// Converts a [`String`] into a `Rec`.
    ///
    /// Inteded for internal use only.
    fn from(other: String) -> Self {
        Self::concatenation(iter::once(other).chain(iter::empty()))
    }
}

/// How two or more [`Element`]s are composed together.
#[derive(Debug, PartialEq)]
enum Composition {
    /// [`Element`]s are appended in order.
    Concatenation,
    /// Each [`Element`] is a possible match.
    ///
    /// The order of the [`Element`]s determines the order by which they are attempted.
    Alternation,
}

impl Atom for char {
    fn to_part(&self) -> String {
        match self {
            // Make sure '-' is not identified as range token.
            '-' => String::from(r"\-"),
            _ => self.to_string(),
        }
    }
}

impl Element for char {
    /// ```
    /// use rec::{prelude::*};
    ///
    /// assert_eq!('?', Rec::from(r"\?"));
    /// ```
    fn to_regex(&self) -> String {
        regex::escape(self.to_string().as_str())
    }

    fn is_atom(&self) -> bool {
        true
    }
}

impl Element for &str {
    fn to_regex(&self) -> String {
        regex::escape(self)
    }

    fn is_atom(&self) -> bool {
        self.parse::<char>().is_ok()
    }
}

impl Compound for &str {}

impl Compound for String {}

impl Element for String {
    fn to_regex(&self) -> String {
        self.clone()
    }

    fn is_atom(&self) -> bool {
        self.parse::<char>().is_ok()
    }
}

/// An enumeration of predefined single character matches.
/// ```
/// use rec::prelude::*;
///
/// assert_eq!("hello" + Class::Digit, Rec::from(r"hello\d"));
/// ```
/// ```
/// use rec::prelude::*;
///
/// assert_eq!('a' + Class::Digit, Rec::from(r"a\d"));
/// ```
// TODO: This test does not belong here
#[derive(AtomOps, Clone, Copy, Debug)]
pub enum Class {
    /// Matches any alphabetic character.
    Alpha,
    /// Matches any alphabetic or numerical digit character.
    AlphaNum,
    /// Matches any numerical digit character.
    Digit,
    /// Matches any whitespace character.
    Whitespace,
    /// Matches any character other than a newline.
    Any,
    /// Matches with the start of the text.
    Start,
    /// Matches with the end of the text.
    End,
    /// Matches with the sign character of a number.
    Sign,
    /// Matches with any digit that is not `0`.
    NonZeroDigit,
    /// Matches with any hexidecimal digit.
    HexDigit,
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

/// Represents a match of one character.
/// ```
/// use rec::prelude::*;
///
/// assert_eq!(Ch::AnyOf("ab") | Ch::AnyOf("cd"), Rec::from("[abcd]"));
/// ```
///
/// ```
/// use rec::prelude::*;
///
/// assert_eq!(Ch::Range('a', 'c') | Ch::AnyOf("xyz"), Rec::from("[a-cxyz]"));
/// ```
/// ```
/// use rec::prelude::*;
///
/// assert_eq!(Ch::AnyOf("ab") | 'c', Rec::from("[abc]"));
/// ```
#[derive(Debug)]
pub enum Ch {
    /// Matches any of the chars in the given &str.
    ///
    /// Used instead of `char | char`, which cannot be implemented.
    ///
    /// # Examples
    /// ```
    /// use rec::prelude::*;
    ///
    /// assert_eq!(Ch::AnyOf("abc"), Rec::from("[abc]"));
    /// ```
    ///
    /// ## `-` is not interpreted as range
    /// ```
    /// use rec::prelude::*;
    ///
    /// assert_eq!(Ch::AnyOf("a-c"), Rec::from(r"[a\-c]"));
    /// ```
    AnyOf(&'static str),
    /// Matches any of the given parts.
    Union(Vec<String>),
    /// Matches any character between (inclusive) the 2 given chars.
    Range(char, char),
}

impl Ch {
    /// ```
    /// use rec::prelude::*;
    ///
    /// assert_eq!(Ch::spread(32, 45), Ch::Range(char::from(32), char::from(45)));
    /// ```
    /// ```
    /// use rec::prelude::*;
    ///
    /// assert_eq!("25" + Ch::Range('0', '5'), Rec::from("25[0-5]"));
    /// ```
    pub fn spread<T: Into<char>>(start: T, end: T) -> Self {
        Ch::Range(start.into(), end.into())
    }

    /// Creates a `Ch` that matches the character with the given numeric value.
    /// ```
    /// use rec::prelude::*;
    ///
    /// assert_eq!(Ch::value(0x20), Ch::AnyOf(" "));
    /// ```
    pub fn value<T: Into<char>>(value: T) -> Self {
        Ch::Union(vec![value.into().to_string()])
    }
}

impl Atom for Ch {
    /// ```
    /// use rec::prelude::*;
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

impl Element for Ch {
    fn to_regex(&self) -> String {
        let part = self.to_part();

        if part.parse::<char>().is_ok() {
            part
        } else {
            format!("[{}]", part)
        }
    }

    fn is_atom(&self) -> bool {
        true
    }
}

/// Provides start and end [`Bound`]s of a repetition.
// Ideally, Repeater would not be needed and repetition would take a RangeBounds<u128>. However,
// u128 does not implement RangeBounds<u128> and both items are defined in std.
pub trait Repeater {
    /// Returns the starting [`Bound`].
    fn start(&self) -> Bound<&u128>;
    /// Returns the ending [`Bound`].
    fn end(&self) -> Bound<&u128>;
}

impl_repeater_for_rangebounds!(RangeFull);
impl_repeater_for_rangebounds!(RangeInclusive<u128>);
impl_repeater_for_rangebounds!(RangeToInclusive<u128>);
impl_repeater_for_rangebounds!(RangeFrom<u128>);

impl Repeater for u128 {
    fn start(&self) -> Bound<&u128> {
        Bound::Included(self)
    }

    fn end(&self) -> Bound<&u128> {
        Bound::Included(self)
    }
}

/// TODO
#[derive(Clone, Copy, Debug)]
pub struct Repeat {
    /// TODO
    range: RepeatRange,
    /// TODO
    eagerness: Eagerness,
}

impl Repeat {
    /// TODO
    const fn new(range: RepeatRange, eagerness: Eagerness) -> Self {
        Self { range, eagerness }
    }
}

impl Display for Repeat {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            match self.range {
                RepeatRange::ZeroOrMore => "*".to_string(),
                RepeatRange::OneOrMore => "+".to_string(),
                RepeatRange::ZeroOrOne => "?".to_string(),
                RepeatRange::Between(start, end) => format!("{{{},{}}}", start, end),
                RepeatRange::AtLeast(min) => format!("{{{},}}", min),
                RepeatRange::Exactly(value) => format!("{{{}}}", value),
            },
            if let RepeatRange::Exactly(_) = self.range {
                ""
            } else {
                match self.eagerness {
                    Eagerness::Greedy => "",
                    Eagerness::Lazy => "?",
                }
            }
        )
    }
}

/// TODO
#[derive(Clone, Copy, Debug)]
pub enum RepeatRange {
    /// TODO
    ZeroOrMore,
    /// TODO
    OneOrMore,
    /// TODO
    ZeroOrOne,
    /// TODO
    Between(u128, u128),
    /// TODO
    AtLeast(u128),
    /// TODO
    Exactly(u128),
}

/// TODO
#[derive(Clone, Copy, Debug)]
pub enum Eagerness {
    /// TODO
    Greedy,
    /// TODO
    Lazy,
}

/// TODO
#[allow(clippy::needless_pass_by_value)] // Not passing by reference makes a better user interface.
pub fn rpt(repeater: impl Repeater) -> RepeatRange {
    match repeater.end() {
        Bound::Unbounded => match repeater.start() {
            Bound::Unbounded => RepeatRange::ZeroOrMore,
            Bound::Included(start) if *start == 1 => RepeatRange::OneOrMore,
            Bound::Included(start) => RepeatRange::AtLeast(*start),
            Bound::Excluded(start) => RepeatRange::AtLeast(start.saturating_add(1)),
        },
        Bound::Included(end) | Bound::Excluded(end) => match repeater.start() {
            Bound::Unbounded if *end == 1 => RepeatRange::ZeroOrOne,
            Bound::Unbounded => RepeatRange::Between(0, *end),
            Bound::Included(start) if *start == *end => RepeatRange::Exactly(*start),
            Bound::Included(start) => RepeatRange::Between(*start, *end),
            Bound::Excluded(start) => RepeatRange::Between(start.saturating_add(1), *end),
        },
    }
}

impl Div<RepeatRange> for char {
    type Output = Rec;

    fn div(self, rhs: RepeatRange) -> Self::Output {
        self.repeat(Repeat::new(rhs, Eagerness::Lazy))
    }
}

impl Mul<RepeatRange> for char {
    type Output = Rec;

    fn mul(self, rhs: RepeatRange) -> Self::Output {
        self.repeat(Repeat::new(rhs, Eagerness::Greedy))
    }
}

impl Mul<RepeatRange> for Class {
    type Output = Rec;

    fn mul(self, rhs: RepeatRange) -> Self::Output {
        self.repeat(Repeat::new(rhs, Eagerness::Greedy))
    }
}
