//! Regular Expression Constructor - the recreational version of regular expressions
//!
//! `rec` is a Rust library that simplifies the process of writing, reading, and using regular
//! expressions. This library is intended for all users working with regular expressions, no matter
//! their familiarity with regular expression syntax. Below is a summary of the functionality
//! provided by `rec`:
//!
//! - WYSIWYG: [`&str`] is interpreted exactly as written (i.e. no metacharacters); all metacharacters
//! (as well as other useful patterns) are provided by the [`Ch`] struct.
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
//! rec = "0.6.0"
//! ```
//!
//! # Examples
//! ## Use Regex API.
//! A [`Pattern`] is a smart pointer to a [`Regex`], so one can call the same functions.
//! ```
//! use rec::{some, Ch, Pattern};
//!
//! let pattern = Pattern::new("hello" + some(Ch::whitespace()) + (Ch::digit() | "world"));
//!
//! assert!(pattern.is_match("hello    world"));
//! ```
//!
//! ## Use Pattern to capture a group.
//! [`Pattern`] additionally provides helper functions to reduce boilerplate.
//! ```
//! use rec::{some, tkn, var, Element, Pattern};
//! use rec::Ch;
//!
//! let decimal_number = Pattern::new(tkn!("whole" => some(Ch::digit())) + "." + var(Ch::digit()));
//!
//! assert_eq!(decimal_number.named_capture_str("23.2", "whole"), Some("23"));
//! ```
//!
//! # FAQ
//!
//! ## I know regular expression syntax; why should I use `rec`?
//!
//! In order for code to be easily maintainable, it should be as simple as possible. Even if the
//! original developer understands their regular expression, it is beneficial for the project as a
//! whole if all contributors are able to easily understand the function of a regular expression.

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
    single_use_lifetimes,
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
    variant_size_differences,
    clippy::cargo,
    clippy::nursery,
    clippy::pedantic
)]
#![allow(single_use_lifetimes)] // issue: rust-lang/rust/#55057

mod base;
mod char;
mod repetition;

pub use crate::base::{Element, Rec};
pub use crate::char::Ch;
pub use crate::repetition::{
    btwn, exact, lazy_btwn, lazy_max, lazy_min, lazy_opt, lazy_some, lazy_var, max, min, opt, some,
    var,
};
pub use regex::{Match, Regex};

use std::ops::Deref;
use std::str::FromStr;

/// Creates a [`Rec`] representing the given [`Element`] assigned a name.
///
/// # Examples
/// ```
/// use rec::{tkn, Element};
/// use rec::Ch;
///
/// let a_rec = tkn!("digit" => Ch::digit());
///
/// assert_eq!(a_rec, String::from(r"(?P<digit>\d)").into_rec())
/// ```
///
/// `tkn!` utilizes named capture groups.
/// ```
/// use rec::{Pattern, tkn, Element, some, Ch};
///
/// let pattern = Pattern::new("name: " + tkn!("name" => some(Ch::any())));
/// let captured_name = pattern.named_capture_str("name: Bob", "name");
///
/// assert_eq!(captured_name, Some("Bob"));
/// ```
#[macro_export]
macro_rules! tkn {
    ($name:expr => $elmt:expr) => {
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
    #[inline]
    pub fn new<T: Element>(element: T) -> Self {
        Self {
            re: element.into_rec().build(),
        }
    }

    /// Returns the [`str`] of the first match in `text`.
    ///
    /// If no match is found, returns [`None`].
    pub fn find_str<'t>(&self, text: &'t str) -> Option<&'t str> {
        self.re.find(text).map(|m| m.as_str())
    }

    /// Returns the [`str`] of the first capture group with `name`.
    ///
    /// If no capture is found or a group with `name` does not exist, returns [`None`].
    pub fn named_capture_str<'t>(&self, text: &'t str, name: &str) -> Option<&'t str> {
        self.re
            .captures(text)
            .and_then(|c| c.name(name).map(|m| m.as_str()))
    }
}

impl Deref for Pattern {
    type Target = Regex;

    fn deref(&self) -> &Self::Target {
        &self.re
    }
}

impl FromStr for Pattern {
    type Err = regex::Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.into_rec().try_build().map(|x| Self { re: x })
    }
}
