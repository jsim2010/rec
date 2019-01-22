//! Regular Expression Constructor.
//!
//! Makes the process of constructing regular expressions easier to accomplish and understand by
//! implementing the following functionality:
//! - WYSIWYG: &str is interpreted exactly as written (i.e. no metacharacters); all metacharacters
//! are provided via the [`ChCls`] enum.
//! - Simple to understand quantifier syntax and capture name syntax.
//! - Overloads operators to provide easy to understand expressions.
//! - [`Pattern`] returns exactly what is requested to reduce boilerplate.
//!
//! Utilizes the [`regex`] crate.
//!
//! # Examples
//! ## Create a Regex
//! You can use [`Rec`] to construct a [`Regex`].
//! ```
//! use rec::{Atom, ChCls, SOME};
//!
//! let a_rec = "hello" + ChCls::WhSpc.rpt(SOME) + (ChCls::Digit | "world");
//! let regex = a_rec.build();
//!
//! assert!(regex.is_match("hello    world"));
//! ```
//!
//! ## Use Pattern to tokenize
//! Instead of using [`Regex`], you can use [`Pattern`] to handle basic matching needs.
//! ```
//! use rec::{Atom, ChCls, VAR, SOME, Pattern};
//!
//! let decimal_number = Pattern::define(ChCls::Digit.rpt(SOME).name("whole") + "." + ChCls::Digit.rpt(VAR));
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
    clippy::nursery,
)]
#![allow(clippy::string_add)]
#![doc(html_root_url = "https://docs.rs/rec/0.2.0")]

// Lint checks currently not defined: missing_doc_code_examples, missing_debug_implementations
// single_use_lifetimes issue: rust-lang/rust/#55057
#![allow(clippy::missing_inline_in_public_items, clippy::needless_pass_by_value)]

use regex::{CaptureMatches, Captures, Match, Matches, Regex};
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::ops::{Add, BitOr};
use std::str::FromStr;

/// [`Quantifier`] that repeats an element zero or more times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const VAR: ConstantQuantifier<'_> = "*";
/// [`Quantifier`] that repeats an element one or more times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const SOME: ConstantQuantifier<'_> = "+";
/// [`Quantifier`] that repeats an element zero or one times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const OPT: ConstantQuantifier<'_> = "?";

/// The symbol added to the end of a quantifier to indicate the quantifier is lazy, i.e. will match
/// as few elements as possible.
const LAZY: &str = "?";

/// Signifies the start of a group.
const GROUP_START: &str = "(?";
/// Signifies the end of a group.
const GROUP_END: &str = ")";
/// Signifies that a group is non-capturing.
const GROUP_NON_CAPTURE: &str = ":";
/// Signifies the start of a group name.
const GROUP_NAMED_START: &str = "P<";
/// Signifies the end of a group name.
const GROUP_NAMED_END: &str = ">";

/// Signifies the start of a character class.
const CHAR_CLASS_START: &str = "[";
/// Signifies the end of a character class.
const CHAR_CLASS_END: &str = "]";
/// Signifies the negation of a character class.
const CHAR_CLASS_NEGATION: &str = "^";

/// Signifies the start of the repetition list.
const REPETITION_START: &str = "{";
/// Signifies the end of the repetition list.
const REPETITION_END: &str = "}";
/// Signifies the delimiter between repetition values.
const REPETITION_DELIMITER: &str = ",";

/// Signifies any digit character '0' - '9'.
const DIGIT_CHAR: &str = r"\d";
/// Signifies any character.
const WILDCARD_CHAR: &str = ".";
/// Signifies any whitespace character.
const WHITESPACE_CHAR: &str = r"\s";
/// Signifies the end of the target string.
const END_CHAR: &str = "$";
/// Signifies the regular expression should match one of two expressions.
const ALTERNATION: &str = "|";

/// Signifies a '.'.
const ESCAPED_PERIOD: &str = r"\.";
/// Signifies a '+'.
const ESCAPED_PLUS: &str = r"\+";
/// Signifies a '*'.
const ESCAPED_STAR: &str = r"\*";

/// Represents a regular expression to be matched against a target.
#[derive(Clone, Debug)]
pub struct Pattern {
    /// The [`Regex`] being used.
    re: Regex,
}

impl Pattern {
    /// Creates a [`Pattern`] from a [`Rec`].
    ///
    /// This is only safe to use with [`Rec`]s that are known prior to runtime.
    ///
    /// # Panics
    ///
    /// Panics if `rec` contains an invalid expression.
    ///
    /// [`Pattern`]: struct.Pattern.html
    /// [`Rec`]: struct.Rec.html
    #[inline]
    pub fn define(rec: Rec) -> Self {
        Self { re: rec.build() }
    }

    /// Attempts to create a [`Pattern`] from a [`Rec`] unknown prior to runtime.
    ///
    /// # Errors
    ///
    /// Returns [`regex::Error`] if attempt is unsuccesful.
    ///
    /// [`Pattern`]: struct.Pattern.html
    /// [`Rec`]: struct.Rec.html
    #[inline]
    pub fn load(rec: &Rec) -> Result<Self, regex::Error> {
        rec.try_build().map(|x| Self { re: x })
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
    pub fn parse<T>(&self, name: &str) -> Result<T, String>
        where T: FromStr,
              T::Err: Display
    {
        self.get(name).ok_or_else(|| String::from("Invalid name")).and_then(|x| x.parse::<T>().map_err(|e| format!("{}", e)))
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
        #[allow(clippy::integer_arithmetic)] // Assume Match keeps end >= start.
        Self { start, length: pattern_match.end() - start }
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

/// Constructs a regular expression.
///
/// This implements the Builder pattern for [`Regex`].
#[derive(Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Rec {
    /// The [`Regexp`] that will be constructed.
    regexp: Regexp,
}

impl Rec {
    /// Creates a [`Rec`] from a [`Regexp`].
    fn with_regexp(regexp: Regexp) -> Self {
        Self { regexp }
    }

    /// Creates a [`Rec`] from the alternation of 2 [`Regexp`]s.
    fn with_alternation(regexp1: Regexp, regexp2: Regexp) -> Self {
        Self::with_regexp(regexp1 + ALTERNATION + &regexp2).group()
    }

    /// Names `self`.
    #[inline]
    pub fn name(self, name: &str) -> Self {
        Self::with_regexp(
            String::from(GROUP_START)
                + GROUP_NAMED_START
                + name
                + GROUP_NAMED_END
                + &self.regexp
                + GROUP_END,
        )
    }

    /// Groups together all of `self`.
    fn group(self) -> Self {
        let length = self.regexp.chars().count();

        if length > 2 || (length == 2 && self.regexp.chars().nth(0) != Some('\\')) {
            return Self::with_regexp(
                String::from(GROUP_START) + GROUP_NON_CAPTURE + &self.regexp + GROUP_END,
            );
        }

        self
    }

    /// Sets how often `self` may be repeated.
    fn quantify(self, quantifier: & impl Quantifier) -> Self {
        Self::with_regexp(self.group().regexp + &quantifier.to_regexp())
    }

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

    /// Attempts to build a [`Regex`] from `self`.
    ///
    /// This is intended to be used with [`Rec`]s that are not known prior to runtime. Otherwise
    /// use [`build`].
    fn try_build(&self) -> Result<Regex, regex::Error> {
        Regex::new(&self.regexp)
    }
}

impl Add for Rec {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self::with_regexp(self.regexp + &other.regexp)
    }
}

impl<T> Add<T> for Rec
where
    T: Atom,
{
    type Output = Self;

    #[inline]
    fn add(self, other: T) -> Self {
        Self::with_regexp(self.regexp + &other.to_regexp())
    }
}

impl BitOr for Rec {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self::with_alternation(self.regexp, rhs.regexp)
    }
}

impl<T> BitOr<T> for Rec
where
    T: Atom,
{
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: T) -> Self {
        Self::with_alternation(self.regexp, rhs.to_regexp())
    }
}

impl Display for Rec {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.regexp)
    }
}

impl Add<Rec> for &'_ str {
    type Output = Rec;

    #[inline]
    fn add(self, other: Rec) -> Rec {
        // &str implements both Atom and Quantifier, which both require to_regexp(). Thus the Atom
        // implementation of to_regexp() must be specified.
        Rec::with_regexp(Atom::to_regexp(&self) + &other.regexp)
    }
}

/// Specifies the characters to be matched against.
pub trait Atom {
    /// Converts `self` to its appropriate [`Regexp`].
    ///
    /// [`Regexp`]: type.Regexp.html
    fn to_regexp(&self) -> Regexp;

    /// Converts `self` to a [`Rec`].
    ///
    /// [`Rec`]: struct.Rec.html
    #[inline]
    fn to_rec(&self) -> Rec {
        Rec::with_regexp(self.to_regexp())
    }

    /// Generates a [`Rec`] consisting of `self` quantified by `quantifier`.
    ///
    /// [`Rec`]: struct.Rec.html
    #[inline]
    fn rpt(&self, quantifier: impl Quantifier) -> Rec {
        self.to_rec().quantify(&quantifier)
    }
}

impl Atom for &'_ str {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        // Escape all metacharacters.
        self.replace(WILDCARD_CHAR, ESCAPED_PERIOD)
            .replace(SOME, ESCAPED_PLUS)
            .replace(VAR, ESCAPED_STAR)
    }
}

/// Specifies a set of characters to be matched against.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ChCls<'a> {
    /// Matches any character except newline.
    Any,
    /// Matches any character except the given characters.
    None(&'a str),
    /// Matches any digit.
    Digit,
    /// Matches any whitespace.
    WhSpc,
    /// Matches the end of the text.
    End,
}

impl Display for ChCls<'_> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let s = match self {
            ChCls::Any => String::from("Any"),
            ChCls::None(chars) => {
                let char_list: Vec<String> = chars.chars().map(|x| x.to_string()).collect();

                String::from("None of {") + &char_list.as_slice().join(",") + "}"
            }
            ChCls::Digit => String::from("Digit"),
            ChCls::WhSpc => String::from("Whitespace"),
            ChCls::End => String::from("End"),
        };
        write!(f, "{}", s)
    }
}

impl Atom for ChCls<'_> {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        match self {
            ChCls::None(chars) => {
                Regexp::from(CHAR_CLASS_START) + CHAR_CLASS_NEGATION + chars + CHAR_CLASS_END
            }
            ChCls::Digit => Regexp::from(DIGIT_CHAR),
            ChCls::Any => Regexp::from(WILDCARD_CHAR),
            ChCls::WhSpc => Regexp::from(WHITESPACE_CHAR),
            ChCls::End => Regexp::from(END_CHAR),
        }
    }
}

impl<T> BitOr<T> for ChCls<'_>
where
    T: Atom,
{
    type Output = Rec;

    #[inline]
    fn bitor(self, rhs: T) -> Rec {
        Rec::with_alternation(self.to_regexp(), rhs.to_regexp())
    }
}

/// Specifies how often an element may be repeated.
///
/// By default, a [`Quantifier`] is greedy, i.e. it will match as many elements as possible. See
/// [`lazy`] for how to make a greedy [`Quantifier`] lazy, i.e. match as few elements
/// as possible.
///
/// [`Quantifier`]: trait.Quantifier.html
/// [`lazy`]: trait.Quantifier.html#method.lazy
pub trait Quantifier {
    /// Converts `self` to its appropriate [`Regexp`].
    ///
    /// [`Regexp`]: type.Regexp.html
    fn to_regexp(&self) -> Regexp;

    /// Makes `self` lazy, i.e. match as few elements as possible.
    ///
    /// # Examples
    /// ```
    /// use rec::{Quantifier, SOME};
    ///
    /// assert_eq!(SOME.lazy(), "+?");
    /// ```
    #[inline]
    fn lazy(&self) -> Repeat {
        self.to_regexp() + LAZY
    }
}

// Implements Quantifier for an exact number of repetitions.
impl Quantifier for usize {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        String::from(REPETITION_START) + &self.to_string() + REPETITION_END
    }
}

// Implements Quantifier for a number of repetitions between 2 numbers.
impl Quantifier for (usize, usize) {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        String::from(REPETITION_START)
            + &self.0.to_string()
            + REPETITION_DELIMITER
            + &self.1.to_string()
            + REPETITION_END
    }
}

// Implements Quantifier for a number of repetitions larger than a number.
impl Quantifier for (usize,) {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        String::from(REPETITION_START) + &self.0.to_string() + REPETITION_DELIMITER + REPETITION_END
    }
}

/// A [`Quantifier`] that is defined before runtime.
///
/// # Examples
/// ```
/// assert_eq!("?", rec::OPT);
/// ```
///
/// [`Quantifier`]: trait.Quantifier.html
pub type ConstantQuantifier<'a> = &'a str;

impl Quantifier for ConstantQuantifier<'_> {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        Regexp::from(*self)
    }
}

/// A [`Regexp`] that functions as a [`Quantifier`].
///
/// [`Regexp`]: type.Regexp.html
/// [`Quantifier`]: trait.Quantifier.html
type Repeat = Regexp;

impl Quantifier for Repeat {
    #[inline]
    fn to_regexp(&self) -> Regexp {
        self.clone()
    }
}

/// A [`String`] that functions as a regular expression.
///
/// [`String`]: https://doc.rust-lang.org/std/string/struct.String.html
type Regexp = String;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_or_more_greedy() {
        let re = "x".rpt(VAR);

        assert_eq!("x*", re.regexp);
    }

    #[test]
    fn one_or_more_greedy() {
        let re = "x".rpt(SOME);

        assert_eq!("x+", re.regexp);
    }

    #[test]
    fn zero_or_one_greedy() {
        let re = "x".rpt(OPT);

        assert_eq!("x?", re.regexp);
    }

    #[test]
    fn zero_or_more_lazy() {
        let re = "x".rpt(VAR.lazy());

        assert_eq!("x*?", re.regexp);
    }

    #[test]
    fn one_or_more_lazy() {
        let re = "x".rpt(SOME.lazy());

        assert_eq!("x+?", re.regexp);
    }

    #[test]
    fn zero_or_one_lazy() {
        let re = "x".rpt(OPT.lazy());

        assert_eq!("x??", re.regexp);
    }

    #[test]
    fn at_least_and_at_most_greedy() {
        let re = "x".rpt((4, 7));

        assert_eq!("x{4,7}", re.regexp);
    }

    #[test]
    fn at_least_greedy() {
        let re = "x".rpt((2,));

        assert_eq!("x{2,}", re.regexp);
    }

    #[test]
    fn exactly() {
        let re = "x".rpt(3);

        assert_eq!("x{3}", re.regexp);
    }

    #[test]
    fn at_least_and_at_most_lazy() {
        let re = "x".rpt((4, 7).lazy());

        assert_eq!("x{4,7}?", re.regexp);
    }

    #[test]
    fn at_least_lazy() {
        let re = "x".rpt((2,).lazy());

        assert_eq!("x{2,}?", re.regexp);
    }

    #[test]
    fn chcls_bitor_str() {
        let re = ChCls::Digit | "a";

        assert_eq!(r"(?:\d|a)", re.regexp);
    }

    #[test]
    fn chcls_bitor_chcls() {
        let re = ChCls::Digit | ChCls::WhSpc;

        assert_eq!(r"(?:\d|\s)", re.regexp);
    }
}
