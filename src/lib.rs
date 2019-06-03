//! Regular Expression Constructor - regular expressions for non-experts
//!
//! `rec` is a Rust library that simplifies the process of writing, reading, and using regular
//! expressions. This library is intended for all users working with regular expressions, no matter
//! their familiarity with regular expression syntax. Below is a summary of the functionality
//! provided by `rec`:
//!
//! - WYSIWYG: `&str` is interpreted exactly as written (i.e. no metacharacters); all metacharacters
//! (as well as other useful patterns) are provided by the [`Ch`] struct.
//! - Simple to understand quantifier and capture group syntaxes.
//! - Uses operators to provide easy to understand expressions.
//! - [`Pattern`] returns exactly what is requested to reduce boilerplate.
//!
//! This library utilizes the [`regex`] crate.
//!
//! # Getting Started
//!
//! Add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rec = "0.4"
//! ```
//!
//! # Examples
//! ## Create a Regex
//! ## Use Pattern to tokenize
//! Instead of using [`Regex`], you can use [`Pattern`] to handle basic matching needs.
//! ```
//! use rec::{some, tkn, var, Element, Pattern};
//! use rec::Ch;
//!
//! let decimal_number = Pattern::new(tkn!(some(Ch::digit()) => "whole") + "." + var(Ch::digit()));
//!
//! assert_eq!(decimal_number.tokenize("23.2").get("whole"), Some("23"));
//! ```
//!
//! If you prefer API of [`regex`], you can use a [`Rec`] to construct a [`Regex`].
//! ```
//! use rec::{some};
//! use rec::Ch;
//!
//! let a_rec = "hello" + some(Ch::whitespace()) + (Ch::digit() | "world");
//! let regex = a_rec.build();
//!
//! assert!(regex.is_match("hello    world"));
//! ```
//!
//! # FAQ
//!
//! ## I know regular expression syntax; why should I use `rec`?
//!
//! In order for code to be easily maintainable, it should be as simple as possible. Even if the
//! original developer understands their regular expression, it is beneficial for the project as a
//! whole if all contributors are able to easily understand the function of a regular expression.
//!
//! [`Ch`]: struct.Ch.html
//! [`Rec`]: struct.Rec.html
//! [`Pattern`]: struct.Pattern.html

#![warn(
    future_incompatible,
    rust_2018_idioms,
    unused,
    box_pointers,
    macro_use_extern_crate,
    missing_copy_implementations,
    missing_debug_implementations,
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
    clippy::cargo,
    clippy::nursery,
    clippy::pedantic,
    clippy::restriction
)]
// Checks that have issues
#![allow(clippy::string_add)]
// Implementing Add for strings provides cleaner code.
// single_use_lifetimes issue: rust-lang/rust/#55057
#![allow(clippy::missing_inline_in_public_items)]
#![allow(clippy::implicit_return)] // Does not follow Rust convention.
#![doc(html_root_url = "https://docs.rs/rec/0.4.0")]

mod base;
mod char;
mod repetition;

pub use crate::base::Element;
pub use crate::char::Ch;
pub use crate::repetition::{
    btwn, exact, lazy_btwn, lazy_min, lazy_opt, lazy_some, lazy_var, min, opt, some, var,
};

use regex::{CaptureMatches, Captures, Match, Matches, Regex};
use std::fmt::{self, Debug, Display, Formatter};
use std::str::FromStr;

/// Creates a [`Rec`] representing the given [`Element`] assigned a name.
///
/// # Examples
/// ```
/// use rec::{tkn, Element};
/// use rec::Ch;
///
/// let a_rec = tkn!(Ch::digit() => "digit");
///
/// assert_eq!(a_rec, String::from(r"(?P<digit>\d)").into_rec())
/// ```
///
/// `tkn!` can be utilized by [`tokenize`].
/// ```
/// use rec::{Pattern, tkn, Element, some};
/// use rec::Ch;
///
/// let pattern = Pattern::new("name: " + tkn!(some(Ch::any()) => "name"));
/// let rec_option = pattern.tokenize("name: Bob").get("name");
///
/// assert_eq!(rec_option, Some("Bob"));
/// ```
#[macro_export]
macro_rules! tkn {
    ($elmt:expr => $name:expr) => {
        format!("(?P<{}>{})", $name, $elmt.into_rec()).into_rec()
    };
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

    /// Returns the first [`Match`] found in the target.
    ///
    /// If no match is found, returns [`None`].
    #[inline]
    pub fn find<'t>(&self, target: &'t str) -> Option<Match<'t>> {
        self.re.find(target)
    }

    /// Returns an [`Iterator`] of each [`Match`] found in the target.
    #[inline]
    pub fn find_iter<'r, 't>(&'r self, target: &'t str) -> Matches<'r, 't> {
        self.re.find_iter(target)
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
    const fn with_captures(captures: Option<Captures<'t>>) -> Tokens<'t> {
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
    const fn with_capture_matches(capture_matches: CaptureMatches<'r, 't>) -> TokensIter<'r, 't> {
        TokensIter { capture_matches }
    }
}

impl Debug for TokensIter<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is currently unhelpful because CaptureMatches does not implement Debug.
        write!(f, "TokensIter")
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chcls_bitor_str() {
        let re = Ch::digit() | "a";

        assert_eq!(re, String::from(r"(?:\d|a)").into_rec());
    }

    #[test]
    fn chcls_bitor_chcls() {
        let re = Ch::digit() | Ch::whitespace();

        assert_eq!(re, String::from(r"(?:\d|\s)").into_rec());
    }
}
