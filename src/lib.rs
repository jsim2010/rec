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
    clippy::pedantic,
    clippy::restriction
)]
#![allow(
    clippy::implicit_return, // Omitting the return keyword is idiomatic Rust code.
    clippy::missing_inline_in_public_items, // Generally not bad and there are issues with derived traits.
)]
#![allow(single_use_lifetimes)] // issue: rust-lang/rust/#55057

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
pub use regex::{Match, Regex};

use crate::prelude::{Element, Rec};
use core::{ops::Deref, str::FromStr};
use regex::Captures;

/// Creates a [`Rec`] representing the given [`Element`] assigned a name.
///
/// # Examples
/// ```
/// use rec::{prelude::*, tkn, Class};
///
/// let a_rec = tkn!("digit" => Class::Digit);
///
/// assert_eq!(a_rec, Rec::from(r"(?P<digit>\d)"))
/// ```
///
/// `tkn!` utilizes named capture groups.
/// ```
/// use rec::{prelude::*, Pattern, tkn, some, Class};
///
/// let pattern = Pattern::new("name: " + tkn!("name" => some(Class::Any)));
/// let captured_name = pattern.name_str("name: Bob", "name");
///
/// assert_eq!(captured_name, Some("Bob"));
/// ```
#[macro_export]
macro_rules! tkn {
    ($name:expr => $elmt:expr) => {
        Rec::from(format!("(?P<{}>{})", $name, $elmt.to_regex()).as_str())
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
    #[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
    pub fn new<T: Element>(element: T) -> Self {
        Self {
            re: Rec::from(element.to_regex()).build(),
        }
    }

    /// Returns the [`str`] of the first [`Match`] in `text`.
    ///
    /// If no match is found, returns [`None`].
    pub fn find_str<'t>(&self, text: &'t str) -> Option<&'t str> {
        self.find(text).map(|m| m.as_str())
    }

    /// Returns the first [`Tokens`] found in `text`.
    pub fn tokenize<'t>(&self, text: &'t str) -> Option<Tokens<'t>> {
        self.captures(text).map(|captures| Tokens { captures })
    }

    /// Returns the [`str`] of the [`Match`] for [`name`] of the first [`Tokens`] found in `text`.
    pub fn name_str<'t>(&self, text: &'t str, name: &str) -> Option<&'t str> {
        // Trying to do `self.tokenize(text).and_then(|t| t.name_str(name))` causes E0515.
        self.tokenize(text)
            .and_then(|t| t.name(name).map(|m| m.as_str()))
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

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Rec::from(s).try_build().map(|x| Self { re: x })
    }
}

/// Stores the found capture groups.
#[derive(Debug)]
pub struct Tokens<'t> {
    /// The [`Captures`] matched from the [`Pattern`].
    captures: Captures<'t>,
}

impl Tokens<'_> {
    /// Returns the [`str`] of the [`Match`] for the given capture name.
    ///
    /// If no match is found, returns [`None`].
    pub fn name_str(&self, name: &str) -> Option<&str> {
        self.name(name).map(|m| m.as_str())
    }
}

impl<'t> Deref for Tokens<'t> {
    type Target = Captures<'t>;

    fn deref(&self) -> &Self::Target {
        &self.captures
    }
}
