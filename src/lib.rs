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

#![doc(html_root_url = "https://docs.rs/rec/0.1.0")]

extern crate regex;

use regex::{CaptureMatches, Captures, Regex};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::{Add, BitOr};

/// [`Quantifier`] that repeats an element zero or more times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const VAR: ConstantQuantifier = "*";
/// [`Quantifier`] that repeats an element one or more times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const SOME: ConstantQuantifier = "+";
/// [`Quantifier`] that repeats an element zero or one times.
///
/// [`Quantifier`]: trait.Quantifier.html
pub const OPT: ConstantQuantifier = "?";

/// The symbol added to the end of a quantifier to indicate the quantifier is lazy, i.e. will match
/// as few elements as possible.
const LAZY: &str = "?";

const GROUP_START: &str = "(?";
const GROUP_END: &str = ")";
const GROUP_NON_CAPTURE: &str = ":";
const GROUP_NAMED_START: &str = "P<";
const GROUP_NAMED_END: &str = ">";

const CHAR_CLASS_START: &str = "[";
const CHAR_CLASS_END: &str = "]";
const CHAR_CLASS_NEGATION: &str = "^";

const REPETITION_START: &str = "{";
const REPETITION_END: &str = "}";
const REPETITION_DELIMITER: &str = ",";

const DIGIT_CHAR: &str = r"\d";
const WILDCARD_CHAR: &str = ".";
const WHITESPACE_CHAR: &str = r"\s";
const END_CHAR: &str = "$";
const ALTERNATION: &str = "|";

const ESCAPED_PERIOD: &str = r"\.";
const ESCAPED_PLUS: &str = r"\+";

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
    /// [`Pattern`]: struct.Pattern.html
    /// [`Rec`]: struct.Rec.html
    ///
    /// # Panics
    ///
    /// Panics if `rec` contains an invalid expression.
    pub fn define(rec: Rec) -> Pattern {
        Pattern { re: rec.build() }
    }

    /// Produces [`Tokens`] that match `self` with given target.
    ///
    /// [`Tokens`]: struct.Tokens.html
    pub fn tokenize<'t>(&self, target: &'t str) -> Tokens<'t> {
        Tokens::with_captures(self.re.captures(target))
    }

    /// Produces an Iterator of [`Tokens`] that match `self` with given target.
    ///
    /// After each [`Tokens`] is produced, the next one is searched from the target after the
    /// current match.
    ///
    /// [`Tokens`]: struct.Tokens.html
    pub fn tokenize_iter<'r, 't>(&'r self, target: &'t str) -> TokensIter<'r, 't> {
        TokensIter::with_capture_matches(self.re.captures_iter(target))
    }
}

impl Default for Pattern {
    fn default() -> Pattern {
        Pattern {
            re: Regex::new("").unwrap(),
        }
    }
}

/// Stores the possible matches of a [`Pattern`] against a target.
///
/// [`Pattern`]: struct.Pattern.html
#[derive(Debug, Default)]
pub struct Tokens<'t> {
    captures: Option<Captures<'t>>,
}

impl<'t> Tokens<'t> {
    /// Creates a new [`Tokens`] from a given [`Captures`].
    fn with_captures(captures: Option<Captures<'t>>) -> Tokens<'t> {
        Tokens { captures }
    }

    /// Retrieves the capture group with the given name.
    pub fn get<'a>(&self, name: &'a str) -> Option<&'t str> {
        self.captures
            .as_ref()
            .and_then(|captures| captures.name(name).map(|x| x.as_str()))
    }
}

/// Iterates through a given target returning each [`Tokens`] found.
pub struct TokensIter<'r, 't> {
    capture_matches: CaptureMatches<'r, 't>,
}

impl<'r, 't> TokensIter<'r, 't> {
    fn with_capture_matches(capture_matches: CaptureMatches<'r, 't>) -> TokensIter<'r, 't> {
        TokensIter { capture_matches }
    }
}

impl<'r, 't> Iterator for TokensIter<'r, 't> {
    type Item = Tokens<'t>;

    fn next(&mut self) -> Option<Tokens<'t>> {
        self.capture_matches
            .next()
            .and_then(|captures| Some(Tokens::with_captures(Some(captures))))
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
    fn with_regexp(regexp: Regexp) -> Rec {
        Rec { regexp }
    }

    /// Creates a [`Rec`] from the alternation of 2 [`Regexp`]s.
    fn with_alternation(regexp1: Regexp, regexp2: Regexp) -> Rec {
        Rec::with_regexp(regexp1 + ALTERNATION + &regexp2).group()
    }

    /// Names `self`.
    pub fn name(self, name: &str) -> Rec {
        Rec::with_regexp(
            String::from(GROUP_START)
                + GROUP_NAMED_START
                + name
                + GROUP_NAMED_END
                + &self.regexp
                + GROUP_END,
        )
    }

    /// Groups together all of `self`.
    fn group(self) -> Rec {
        let length = self.regexp.chars().count();

        if length > 2 || (length == 2 && self.regexp.chars().nth(0) != Some('\\')) {
            return Rec::with_regexp(
                String::from(GROUP_START) + GROUP_NON_CAPTURE + &self.regexp + GROUP_END,
            );
        }

        self
    }

    /// Sets how often `self` may be repeated.
    fn quantify(self, quantifier: impl Quantifier) -> Rec {
        Rec::with_regexp(self.group().regexp + &quantifier.to_regexp())
    }

    /// Builds a [`Regex`] from `self`.
    ///
    /// This is only safe to use with [`Rec`]s that are known prior to runtime. Otherwise use
    /// [`try_build`].
    ///
    /// # Panics
    /// Panics if `self` contains an invalid expression.
    pub fn build(&self) -> Regex {
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
    type Output = Rec;

    fn add(self, other: Rec) -> Rec {
        Rec::with_regexp(self.regexp + &other.regexp)
    }
}

impl<T> Add<T> for Rec
where
    T: Atom,
{
    type Output = Rec;

    fn add(self, other: T) -> Rec {
        Rec::with_regexp(self.regexp + &other.to_regexp())
    }
}

impl BitOr for Rec {
    type Output = Rec;

    fn bitor(self, rhs: Rec) -> Rec {
        Rec::with_alternation(self.regexp, rhs.regexp)
    }
}

impl<T> BitOr<T> for Rec
where
    T: Atom,
{
    type Output = Rec;

    fn bitor(self, rhs: T) -> Rec {
        Rec::with_alternation(self.regexp, rhs.to_regexp())
    }
}

impl Display for Rec {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.regexp)
    }
}

impl<'a> Add<Rec> for &'a str {
    type Output = Rec;

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
    fn to_rec(&self) -> Rec {
        Rec::with_regexp(self.to_regexp())
    }

    /// Generates a [`Rec`] consisting of `self` quantified by `quantifier`.
    ///
    /// [`Rec`]: struct.Rec.html
    fn rpt(&self, quantifier: impl Quantifier) -> Rec {
        self.to_rec().quantify(quantifier)
    }
}

impl<'a> Atom for &'a str {
    fn to_regexp(&self) -> Regexp {
        // Escape all metacharacters.
        self.replace(WILDCARD_CHAR, ESCAPED_PERIOD)
            .replace(SOME, ESCAPED_PLUS)
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

impl<'a> Display for ChCls<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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

impl<'a> Atom for ChCls<'a> {
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

impl<'a, T> BitOr<T> for ChCls<'a>
where
    T: Atom,
{
    type Output = Rec;

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
    fn lazy(&self) -> Repeat {
        Repeat::from(self.to_regexp() + LAZY)
    }
}

// Implements Quantifier for an exact number of repetitions.
impl Quantifier for usize {
    fn to_regexp(&self) -> Regexp {
        String::from(REPETITION_START) + &self.to_string() + REPETITION_END
    }
}

// Implements Quantifier for a number of repetitions between 2 numbers.
impl Quantifier for (usize, usize) {
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

impl<'a> Quantifier for ConstantQuantifier<'a> {
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
