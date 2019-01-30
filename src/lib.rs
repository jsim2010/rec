//! Regular Expression Constructor - making working with regular expressions fun
//!
//! Makes the process of constructing regular expressions easier to accomplish and understand by
//! implementing the following functionality:
//! - WYSIWYG: &str is interpreted exactly as written (i.e. no metacharacters); all metacharacters
//! (as well as some other useful patterns) are provided via the [`ChCls`] enum.
//! - Simple to understand quantifier syntax and capture name syntax.
//! - Overloads operators to provide easy to understand expressions.
//! - [`Pattern`] returns exactly what is requested to reduce boilerplate.
//!
//! Utilizes the [`regex`] crate.
//!
//! # Examples
//! ## Create a Regex
//! If you prefer API of [`regex`], you can use a [`Rec`] to construct a [`Regex`].
//! ```
//! use rec::{some};
//! use rec::ChCls::{Digit, Whitespace};
//!
//! let a_rec = "hello" + some(Whitespace) + (Digit | "world");
//! let regex = a_rec.build();
//!
//! assert!(regex.is_match("hello    world"));
//! ```
//!
//! ## Use Pattern to tokenize
//! Instead of using [`Regex`], you can use [`Pattern`] to handle basic matching needs.
//! ```
//! use rec::{some, tkn, var, Element, Pattern};
//! use rec::ChCls::Digit;
//!
//! let decimal_number = Pattern::new(tkn!(some(Digit) => "whole") + "." + var(Digit));
//!
//! assert_eq!(decimal_number.tokenize("23.2").get("whole"), Some("23"));
//! ```
//!
//! [`ChCls`]: enum.ChCls.html
//! [`Rec`]: struct.Rec.html
//! [`Pattern`]: struct.Pattern.html

#![warn(
    future_incompatible,
    rust_2018_idioms,
    unused,
    box_pointers,
    macro_use_extern_crate,
    missing_copy_implementations,
    missing_docs,
    missing_doc_code_examples,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications,
    unused_results,
    variant_size_differences,
    clippy::restriction,
    clippy::pedantic,
    clippy::nursery
)]
#![allow(clippy::string_add)]
#![doc(html_root_url = "https://docs.rs/rec/0.3.0")]
// Lint checks currently not defined: missing_debug_implementations
// single_use_lifetimes issue: rust-lang/rust/#55057
#![allow(clippy::missing_inline_in_public_items)]

use regex::{CaptureMatches, Captures, Match, Matches, Regex};
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::ops::{Add, BitOr};
use std::str::FromStr;

/// Creates a capture group with a given name.
///
/// # Examples
/// `tkn!` macro generates a named capture group.
/// ```
/// use rec::{tkn, Element};
/// use rec::ChCls::Digit;
///
/// let token = tkn!(Digit => "digit");
/// assert_eq!(format!("{}", token), r"(?P<digit>\d)")
/// ```
///
/// `tkn!` can be utilized by [`tokenize`].
/// ```
/// use rec::{Pattern, tkn, Element, some};
/// use rec::ChCls::Any;
///
/// let pattern = Pattern::new("name: " + tkn!(some(Any) => "name"));
///
/// assert_eq!(pattern.tokenize("name: Bob").get("name"), Some("Bob"));
/// ```
#[macro_export]
macro_rules! tkn {
    ($elmt:expr => $name:expr) => {
        format!("(?P<{}>{})", $name, $elmt.into_rec()).into_rec()
    };
}

macro_rules! rpt {
    ($elmt:expr, $rep:expr) => {
        Rec(format!("{}{}", $elmt.into_rec().group(), $rep))
    };
}

macro_rules! lazy {
    ($rec:expr) => {
        Rec(format!("{}?", $rec))
    };
}

macro_rules! var {
    ($elmt:expr) => {
        rpt!($elmt, SYMBOL_VAR)
    };
}

macro_rules! some {
    ($elmt:expr) => {
        rpt!($elmt, SYMBOL_SOME)
    };
}

macro_rules! opt {
    ($elmt:expr) => {
        rpt!($elmt, SYMBOL_OPT)
    };
}

macro_rules! quantifier {
    ($qty:expr) => {
        format!("{{{}}}", $qty)
    };
}

macro_rules! btwn {
    ($min:expr, $max:expr, $elmt:expr) => {
        rpt!($elmt, quantifier!(format!("{},{}", $min, $max)))
    };
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or more times.
///
/// # Examples
/// ```
/// use rec::var;
///
/// assert_eq!(format!("{}", var("x")), "x*");
/// ```
#[inline]
pub fn var<T: Element>(element: T) -> Rec {
    var!(element)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or more of times.
///
/// # Examples
/// ```
/// use rec::lazy_var;
///
/// assert_eq!(format!("{}", lazy_var("x")), "x*?");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn lazy_var<T: Element>(element: T) -> Rec {
    lazy!(var!(element))
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::some;
///
/// assert_eq!(format!("{}", some("x")), "x+");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn some<T: Element>(element: T) -> Rec {
    some!(element)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::lazy_some;
///
/// assert_eq!(format!("{}", lazy_some("x")), "x+?");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn lazy_some<T: Element>(element: T) -> Rec {
    lazy!(some!(element))
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::opt;
///
/// assert_eq!(format!("{}", opt("x")), "x?");
/// ```
#[inline]
pub fn opt<T: Element>(element: T) -> Rec {
    opt!(element)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::lazy_opt;
///
/// assert_eq!(format!("{}", lazy_opt("x")), "x??");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn lazy_opt<T: Element>(element: T) -> Rec {
    lazy!(opt!(element))
}

/// Returns a [`Rec`] representing the given [`Element`] repeated a given number of times.
///
/// # Examples
/// ```
/// use rec::exact;
///
/// assert_eq!(format!("{}", exact(3, "x")), "x{3}");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn exact<T: Element>(quantity: usize, element: T) -> Rec {
    rpt!(element, quantifier!(quantity))
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::min;
///
/// assert_eq!(format!("{}", min(2, "x")), "x{2,}");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn min<T: Element>(quantity: usize, element: T) -> Rec {
    btwn!(quantity, INFINITY, element)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::lazy_min;
///
/// assert_eq!(format!("{}", lazy_min(2, "x")), "x{2,}?");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn lazy_min<T: Element>(quantity: usize, element: T) -> Rec {
    lazy!(btwn!(quantity, INFINITY, element))
}

/// Returns a [`Rec`] representing the given [`Element`] repeated between 2 numbers.
/// 
/// # Examples
/// ```
/// use rec::btwn;
///
/// assert_eq!(format!("{}", btwn(4, 7, "x")), "x{4,7}");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    btwn!(min, max, element)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated a range of given times.
///
/// # Examples
/// ```
/// use rec::lazy_btwn;
///
/// assert_eq!(format!("{}", lazy_btwn(4, 7, "x")), "x{4,7}?");
/// ```
///
/// [`Rec`]: struct.Rec.html
/// [`Element`]: trait.Element.html
#[inline]
pub fn lazy_btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    lazy!(btwn!(min, max, element))
}

/// Represents a regular expression to be matched against a target.
#[derive(Clone, Debug)]
pub struct Pattern {
    /// The [`Regex`] being used.
    re: Regex,
}

impl Pattern {
    /// Creates a [`Pattern`].
    ///
    /// This is only safe to use with [`Element`]s that are known prior to runtime.
    ///
    /// # Panics
    ///
    /// Panics if `element` converts into a [`Rec`] with an invalid regular expression.
    ///
    /// [`Pattern`]: struct.Pattern.html
    /// [`Rec`]: struct.Rec.html
    /// [`Element`]: trait.Element.html
    #[inline]
    pub fn new<T: Element>(element: T) -> Self {
        Self {
            re: element.into_rec().build(),
        }
    }

    /// Produces [`Tokens`] that match `self` with given target.
    ///
    /// [`Tokens`]: struct.Tokens.html
    #[inline]
    pub fn tokenize<'t>(&self, target: &'t str) -> Tokens<'t> {
        Tokens::with_captures(self.re.captures(target))
    }

    /// Produces an Iterator of [`Tokens`] that match `self` with given target.
    ///
    /// After each [`Tokens`] is produced, the next one is searched from the target after the
    /// current match.
    ///
    /// [`Tokens`]: struct.Tokens.html
    #[inline]
    pub fn tokenize_iter<'r, 't>(&'r self, target: &'t str) -> TokensIter<'r, 't> {
        TokensIter::with_capture_matches(self.re.captures_iter(target))
    }

    /// Produces [`Location`] of the match.
    ///
    /// If no match is found, returns [`None`].
    ///
    /// [`Location`]: struct.Location.html
    #[inline]
    pub fn locate(&self, target: &str) -> Option<Location> {
        self.re.find(target).map(Location::with_match)
    }

    /// Produces [`Locations`] that match `self` with given target.
    ///
    /// After each [`Location`] is produced, the next one is searched from the target after the
    /// current match.
    ///
    /// [`Location`]: struct.Location.html
    /// [`Locations`]: struct.Locations.html
    #[inline]
    pub fn locate_iter<'r, 't>(&'r self, target: &'t str) -> Locations<'r, 't> {
        Locations::with_matches(self.re.find_iter(target))
    }
}

impl FromStr for Pattern {
    type Err = regex::Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.into_rec().try_build().map(|x| Self { re: x })
    }
}

/// Stores the possible matches of a [`Pattern`] against a target.
///
/// [`Pattern`]: struct.Pattern.html
#[derive(Debug, Default)]
pub struct Tokens<'t> {
    /// The tokenized matches.
    captures: Option<Captures<'t>>,
}

impl<'t> Tokens<'t> {
    /// Creates a new [`Tokens`] from a given [`Captures`].
    fn with_captures(captures: Option<Captures<'t>>) -> Tokens<'t> {
        Tokens { captures }
    }

    /// Retrieves the capture group with the given name.
    #[inline]
    pub fn get(&self, name: &str) -> Option<&'t str> {
        self.captures
            .as_ref()
            .and_then(|captures| captures.name(name).map(|x| x.as_str()))
    }

    /// Retrieves and parses the capture group with the given name.
    #[inline]
    pub fn parse<T>(&self, name: &str) -> Result<T, String>
    where
        T: FromStr,
        T::Err: Display,
    {
        self.get(name)
            .ok_or_else(|| String::from("Invalid name"))
            .and_then(|x| x.parse::<T>().map_err(|e| format!("{}", e)))
    }
}

/// Iterates through a given target returning each [`Tokens`] found.
pub struct TokensIter<'r, 't> {
    /// The [`Iterator`] of tokenized matches.
    capture_matches: CaptureMatches<'r, 't>,
}

impl<'r, 't> TokensIter<'r, 't> {
    /// Creates a new [`TokensIter`] from a given [`CaptureMatches`].
    fn with_capture_matches(capture_matches: CaptureMatches<'r, 't>) -> TokensIter<'r, 't> {
        TokensIter { capture_matches }
    }
}

impl<'t> Iterator for TokensIter<'_, 't> {
    type Item = Tokens<'t>;

    #[inline]
    fn next(&mut self) -> Option<Tokens<'t>> {
        self.capture_matches
            .next()
            .and_then(|captures| Some(Tokens::with_captures(Some(captures))))
    }
}

/// Iterates through a target, returning the [`Location`] of each match.
pub struct Locations<'r, 't> {
    /// The iterator of [`Match`]s to be converted to [`Location`]s.
    matches: Matches<'r, 't>,
}

impl<'r, 't> Locations<'r, 't> {
    /// Creates a [`Locations`] from a given [`Matches`].
    fn with_matches(matches: Matches<'r, 't>) -> Locations<'r, 't> {
        Locations { matches }
    }
}

impl Iterator for Locations<'_, '_> {
    type Item = Location;

    #[inline]
    fn next(&mut self) -> Option<Location> {
        self.matches.next().map(Location::with_match)
    }
}

/// Represents where in the target that a match was found.
#[derive(Debug, Copy, Clone)]
pub struct Location {
    /// The byte index where the match begins.
    start: usize,
    /// The number of bytes that make up the match in the target.
    length: usize,
}

impl Location {
    /// Creates a [`Location`] from a given [`Match`].
    fn with_match(pattern_match: Match<'_>) -> Self {
        let start = pattern_match.start();
        #[allow(clippy::integer_arithmetic)] // Assume Match ensures end >= start.
        Self {
            start,
            length: pattern_match.end() - start,
        }
    }

    /// Returns the start of the match.
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns the length of the match.
    #[inline]
    pub fn length(&self) -> usize {
        self.length
    }
}

/// Signifies elements that can be converted into a [`Rec`].
pub trait Element {
    /// Converts element into a [`Rec`].
    fn into_rec(self) -> Rec;
}

impl Element for String {
    #[inline]
    fn into_rec(self) -> Rec {
        Rec(self)
    }
}

impl Element for &str {
    #[inline]
    fn into_rec(self) -> Rec {
        Rec(self
            .replace(SYMBOL_WILDCARD, ESCAPED_PERIOD)
            .replace(SYMBOL_SOME, ESCAPED_PLUS)
            .replace(SYMBOL_VAR, ESCAPED_STAR)
            .replace(SYMBOL_OPT, ESCAPED_QUESTION_MARK)
            .replace(SYMBOL_ALTERNATION, ESCAPED_BAR))
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
    #[allow(clippy::result_unwrap_used)] // It is desired to panic on an error.
    #[inline]
    pub fn build(self) -> Regex {
        self.try_build().unwrap()
    }

    /// Groups together all of `self`.
    fn group(self) -> Self {
        let length = self.0.chars().count();

        if length > 2 || (length == 2 && self.0.chars().nth(0) != Some('\\')) {
            return Rec("(?:".to_string() + &self.0 + ")");
        }

        self
    }

    /// Attempts to build a [`Regex`] from `self`.
    ///
    /// This is intended to be used with [`Rec`]s that are not known prior to runtime. Otherwise
    /// use [`build`].
    fn try_build(&self) -> Result<Regex, regex::Error> {
        Regex::new(&self.0)
    }
}

impl Element for Rec {
    #[inline]
    fn into_rec(self) -> Self {
        self
    }
}

impl<T: Element> Add<T> for Rec {
    type Output = Self;

    #[inline]
    fn add(self, other: T) -> Self {
        Rec(self.0 + &other.into_rec().0)
    }
}

impl<T: Element> BitOr<T> for Rec {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: T) -> Self {
        let new = Self(self.0 + SYMBOL_ALTERNATION + &rhs.into_rec().0);
        new.group()
    }
}

impl Display for Rec {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    #[inline]
    fn add(self, other: Rec) -> Rec {
        Rec(self.to_string() + &other.0)
    }
}

/// Specifies a set of characters to be matched against.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ChCls<'a> {
    /// Matches any character except newline.
    Any,
    /// Matches any character except the given characters.
    Not(&'a str),
    /// Matches any digit.
    Digit,
    /// Matches any whitespace.
    Whitespace,
    /// Matches the end of the text.
    End,
    /// Matches `+` or `-`.
    Sign,
}

impl Element for ChCls<'_> {
    #[inline]
    fn into_rec(self) -> Rec {
        Rec(match self {
            ChCls::Any => String::from(SYMBOL_WILDCARD),
            ChCls::Not(chars) => format!("[^{}]", chars),
            ChCls::Digit => String::from(r"\d"),
            ChCls::Whitespace => String::from(r"\s"),
            ChCls::End => String::from("$"),
            ChCls::Sign => String::from(r"(\+|-)"),
        })
    }
}

impl<T: Element> Add<T> for ChCls<'_> {
    type Output = Rec;

    #[inline]
    fn add(self, other: T) -> Rec {
        self.into_rec() + other
    }
}

impl<T: Element> BitOr<T> for ChCls<'_> {
    type Output = Rec;

    #[inline]
    fn bitor(self, rhs: T) -> Rec {
        self.into_rec() | rhs
    }
}

impl Display for ChCls<'_> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let s = match self {
            ChCls::Any => String::from("Any"),
            ChCls::Not(chars) => {
                let char_list: Vec<String> = chars.chars().map(|x| x.to_string()).collect();

                String::from("Not {") + &char_list.as_slice().join(",") + "}"
            }
            ChCls::Digit => String::from("Digit"),
            ChCls::Whitespace => String::from("Whitespace"),
            ChCls::End => String::from("End"),
            ChCls::Sign => String::from("Plus or Minus"),
        };
        write!(f, "{}", s)
    }
}

/// Signifies an element is repeated zero or more times.
const SYMBOL_VAR: &str = "*";
/// Signifies an element is repeated one or more times.
const SYMBOL_SOME: &str = "+";
/// Signifies an element is repeated zero or one time.
const SYMBOL_OPT: &str = "?";
/// Signifies any character.
const SYMBOL_WILDCARD: &str = ".";
/// Signifies the regular expression should match one of two expressions.
const SYMBOL_ALTERNATION: &str = "|";

/// Signifies a '.'.
const ESCAPED_PERIOD: &str = r"\.";
/// Signifies a '+'.
const ESCAPED_PLUS: &str = r"\+";
/// Signifies a '*'.
const ESCAPED_STAR: &str = r"\*";
/// Signifies a '?'.
const ESCAPED_QUESTION_MARK: &str = r"\?";
/// Signifies a '|'.
const ESCAPED_BAR: &str = r"\|";

/// Signifies not setting a max value in a quantifier.
const INFINITY: &str = "";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chcls_bitor_str() {
        let re = ChCls::Digit | "a";

        assert_eq!(r"(?:\d|a)", re.0);
    }

    #[test]
    fn chcls_bitor_chcls() {
        let re = ChCls::Digit | ChCls::Whitespace;

        assert_eq!(r"(?:\d|\s)", re.0);
    }
}
