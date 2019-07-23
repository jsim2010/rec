//! Regular Expression Constructor - the recreational version of regular expressions
//!
//! `rec` is a Rust library that simplifies the process of writing, reading, and using regular
//! expressions. This library is intended for all users working with regular expressions, no matter
//! their familiarity with regular expression syntax. Below is a summary of the functionality
//! provided by `rec`:
//!
//! - WYSIWYG: [`&str`] and [`char`] are interpreted exactly as written (i.e. no metacharacters);
//! all metacharacters (as well as other useful patterns) are provided by the [`Class`] struct.
//! - Simple to understand quantifier and capture group syntaxes.
//! - Uses operators to provide easy to understand expressions.
//! - [`Pattern`] expands on [`Regex`] API to simplify access to data.
//!
//! This library utilizes the [`regex`] crate.
//!
//! # Getting Started
//!
//! Add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rec = "0.10.0"
//! ```
//!
//! # Examples
//! ## Use Regex API.
//!
//! A [`Pattern`] is a smart pointer to a [`Regex`], so one can call the same functions.
//!
//! ```
//! use rec::{some, Class, Pattern};
//!
//! let pattern = Pattern::new("hello" + some(Class::Whitespace) + (Class::Digit | "world"));
//!
//! assert!(pattern.is_match("hello    world"));
//! ```
//!
//! ## Use Pattern to capture a group.
//!
//! [`Pattern`] additionally provides helper functions to reduce boilerplate.
//!
//! ```
//! use rec::{prelude::*, some, tkn, var, Class, Pattern};
//!
//! let decimal_number = Pattern::new(tkn!("whole" => some(Class::Digit)) + "." + var(Class::Digit));
//!
//! assert_eq!(decimal_number.name_str("23.2", "whole"), Some("23"));
//! ```
//!
//! # FAQ
//!
//! ## I know regular expression syntax; why should I use `rec`?
//!
//! In order for code to be easily maintainable, it should be as simple as possible. Even if the
//! original developer understands their regular expression, it is beneficial for the project as a
//! whole if all contributors are able to easily understand the function of a regular expression.

#![no_std]
#![warn(
    absolute_paths_not_starting_with_crate,
    anonymous_parameters,
    bare_trait_objects,
    box_pointers,
    deprecated_in_future,
    elided_lifetimes_in_paths,
    ellipsis_inclusive_range_patterns,
    explicit_outlives_requirements,
    keyword_idents,
    macro_use_extern_crate,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    missing_doc_code_examples,
    private_doc_tests,
    question_mark_macro_sep,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_code,
    unstable_features,
    unused_extern_crates,
    unused_import_braces,
    unused_labels,
    unused_lifetimes,
    unused_qualifications,
    unused_results,
    clippy::cargo,
    clippy::nursery,
    clippy::pedantic,
    clippy::restriction
)]
// Rustc lints that are not warned:
// single_use_lifetimes: there are issues with derived traits
// variant_size_differences: generally there is not much that can be done about this
#![allow(
    clippy::suspicious_op_assign_impl,
    clippy::suspicious_arithmetic_impl,
    clippy::fallible_impl_from, // Above lints are not always correct; issues should be detected by tests or other lints.
    clippy::implicit_return, // Omitting the return keyword is idiomatic Rust code.
    clippy::missing_inline_in_public_items, // Generally not bad and there are issues with derived traits.
)]

extern crate alloc;

pub mod prelude;

mod atom;
mod repetition;

pub use crate::{
    atom::{Ch, Class},
    repetition::{
        btwn, exact, lazy_btwn, lazy_max, lazy_min, lazy_opt, lazy_some, lazy_var, max, min, opt,
        some, var,
    },
};

use crate::prelude::{Element, Rec};
use core::{ops::Deref, str::FromStr};
use regex::{Captures, Regex};

/// Creates a [`Rec`] representing an [`Element`] that has been assigned a name.
///
/// # Examples
/// `tkn!` implements the named capture group syntax of `regex`.
/// ```
/// use rec::{prelude::*, tkn, Class};
///
/// let a_rec = tkn!("digit" => Class::Digit);
///
/// assert_eq!(a_rec, Rec::from(r"(?P<digit>\d)"))
/// ```
///
/// [`Pattern`] provides convenient functions for accessing values from tokens.
/// ```
/// use rec::{prelude::*, Pattern, tkn, some, Class};
///
/// let pattern = Pattern::new("name: " + tkn!("person" => some(Class::Any)));
///
/// assert_eq!(pattern.name_str("name: Bob", "person"), Some("Bob"));
/// ```
#[macro_export]
macro_rules! tkn {
    ($name:expr => $elmt:expr) => {
        Rec::from(format!("(?P<{}>{})", $name, $elmt.to_regex()).as_str())
    };
}

/// A regular expression to be matched against an input string.
#[derive(Clone, Debug)]
pub struct Pattern {
    /// The regular expression.
    re: Regex,
}

impl Pattern {
    /// Creates a new `Pattern`.
    ///
    /// This is only safe to use with [`Element`]s that are known prior to runtime. Otherwise, use
    /// [`str::parse`]
    ///
    /// # Panics
    ///
    /// Panics if [`Rec`] from `element` is invalid.
    #[allow(clippy::needless_pass_by_value)] // User interface is simpler when passing by value.
    pub fn new<T: Element>(element: T) -> Self {
        Self {
            re: Rec::from(element.to_regex()).build(),
        }
    }

    /// Returns the matched text of the first [`Match`] in `input`.
    ///
    /// [`None`] indicates no [`Match`] was found.
    ///
    /// # Examples
    ///
    /// ```
    /// use rec::{Class, Pattern};
    ///
    /// let pattern = Pattern::new(Class::Digit);
    ///
    /// assert_eq!(pattern.find_str("test5"), Some("5"));
    /// ```
    pub fn find_str<'t>(&self, input: &'t str) -> Option<&'t str> {
        self.find(input).map(|mtch| mtch.as_str())
    }

    /// Returns the first [`Tokens`] found in `input`.
    ///
    /// [`None`] indicates no [`Tokens`] was found.
    ///
    /// # Examples
    ///
    /// Used for accessing multiple [`Match`]es within a single [`Tokens`], without building the
    /// [`Tokens`] each time. If only accessing the text of a single [`Match`], see [`name_str`].
    /// ```
    /// use rec::{tkn, prelude::*, Class, Pattern};
    ///
    /// let pattern = Pattern::new(tkn!("field" => Class::Alpha) + ':' + tkn!("value" => Class::Digit));
    /// let tokens = pattern.tokenize("a:1").unwrap();
    ///
    /// assert_eq!(tokens.name_str("field"), Some("a"));
    /// assert_eq!(tokens.name_str("value"), Some("1"));
    /// ```
    pub fn tokenize<'t>(&self, input: &'t str) -> Option<Tokens<'t>> {
        self.captures(input).map(Tokens::from)
    }

    /// Returns the matched text with token `name` in the first [`Tokens`] found in `input`.
    ///
    /// [`None`] indicates either no [`Tokens`] was found or one was found but it did not contain
    /// the token `name`.
    ///
    /// # Examples
    ///
    /// Used for accessing the text of single [`Match`]. If accessing multiple [`Match`]es, see
    /// [`tokenize`].
    /// ```
    /// use rec::{tkn, prelude::*, Class, Pattern};
    ///
    /// let pattern = Pattern::new("v:" + tkn!("value" => Class::Digit));
    ///
    /// assert_eq!(pattern.name_str("v:4", "value"), Some("4"));
    /// ```
    pub fn name_str<'t>(&self, input: &'t str, name: &str) -> Option<&'t str> {
        self.tokenize(input)
            .and_then(|tokens| tokens.name_str(name))
    }
}

impl Deref for Pattern {
    type Target = Regex;

    fn deref(&self) -> &Self::Target {
        &self.re
    }
}

impl From<Regex> for Pattern {
    fn from(other: Regex) -> Self {
        Self { re: other }
    }
}

impl FromStr for Pattern {
    type Err = regex::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Rec::from(s).try_build().map(Self::from)
    }
}

/// Stores the matches from named capture groups.
///
/// `'t` is the lifetime of the input string.
#[derive(Debug)]
pub struct Tokens<'t> {
    /// The matches from named capture groups.
    captures: Captures<'t>,
}

impl<'t> Tokens<'t> {
    /// Returns the matched text with token `name`.
    ///
    /// [`None`] indicates no `name` token was found.
    pub fn name_str(&self, name: &str) -> Option<&'t str> {
        self.name(name).map(|m| m.as_str())
    }

    /// Returns the `T` parsed from the matched text with token `name`.
    ///
    /// [`None`] indicates no `name` token was found. `Some(Err)` indicates matched text was
    /// unable to be parsed into `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rec::{prelude::*, some, tkn, Class, Pattern};
    ///
    /// let pattern = Pattern::new(tkn!("u8" => some(Class::Digit)));
    /// let tokens = pattern.tokenize("42").unwrap();
    ///
    /// assert_eq!(tokens.name_parse("u8"), Some(Ok(42)));
    /// ```
    pub fn name_parse<T>(&self, name: &str) -> Option<Result<T, <T as FromStr>::Err>>
    where
        T: FromStr,
    {
        self.name_str(name).map(str::parse::<T>)
    }
}

impl<'t> Deref for Tokens<'t> {
    type Target = Captures<'t>;

    fn deref(&self) -> &Self::Target {
        &self.captures
    }
}

impl<'t> From<Captures<'t>> for Tokens<'t> {
    fn from(other: Captures<'t>) -> Self {
        Self { captures: other }
    }
}
