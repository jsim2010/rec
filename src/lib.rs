//! Regular Expression Constructor - the recreational version of regular expressions
////!
////! `rec` is a Rust library that simplifies the process of writing, reading, and using regular
////! expressions. This library is intended for all users working with regular expressions, no matter
////! their familiarity with regular expression syntax. Below is a summary of the functionality
////! provided by `rec`:
////!
////! - WYSIWYG: [`&str`] and [`char`] are interpreted exactly as written (i.e. no metacharacters);
////! all metacharacters (as well as other useful patterns) are provided by the [`Class`] struct.
////! - Simple to understand quantifier and capture group syntaxes.
////! - Uses operators to provide easy to understand expressions.
////! - [`Pattern`] expands on [`Regex`] API to simplify access to data.
////!
////! This library utilizes the [`regex`] crate.
////!
////! # Getting Started
////!
////! Add the following to your `Cargo.toml`:
////!
////! ```toml
////! [dependencies]
////! rec = "0.10.0"
////! ```
////!
////! # Examples
////! ## Use Regex API.
////!
////! A [`Pattern`] is a smart pointer to a [`Regex`], so one can call the same functions.
////!
////! ```
////! use rec::{prelude::*, Pattern};
////!
////! let pattern = Pattern::new("hello" + Class::Whitespace * rpt(1..) + (Class::Digit | "world"));
////!
////! assert!(pattern.is_match("hello    world"));
////! ```
////!
////! ## Use Pattern to capture a group.
////!
////! [`Pattern`] additionally provides helper functions to reduce boilerplate.
////!
////! ```
////! use rec::{prelude::*, tkn, Pattern};
////!
////! let decimal_number = Pattern::new(tkn!("whole" => Class::Digit * rpt(1..)) + "." + Class::Digit * rpt(..));
////!
////! assert_eq!(decimal_number.name_str("23.2", "whole"), Some("23"));
////! ```
////!
////! # FAQ
////!
////! ## I know regular expression syntax; why should I use `rec`?
////!
////! In order for code to be easily maintainable, it should be as simple as possible. Even if the
////! original developer understands their regular expression, it is beneficial for the project as a
////! whole if all contributors are able to easily understand the function of a regular expression.

#![warn(
    absolute_paths_not_starting_with_crate,
    anonymous_parameters,
    bare_trait_objects,
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
// box_pointers: boxes are generally okay
// single_use_lifetimes: there are issues with derived traits
// variant_size_differences: generally there is not much that can be done about this
#![allow(
    clippy::suspicious_op_assign_impl,
    clippy::suspicious_arithmetic_impl,
    clippy::fallible_impl_from, // Above lints assume a given use; issues should be detected by tests or other lints.
    clippy::implicit_return, // Omitting the return keyword is idiomatic Rust code.
    clippy::missing_inline_in_public_items, // There are issues with derived traits.
)]
//#![no_std]

extern crate proc_macro;

use core::{convert::TryFrom, ops::Deref};
use lazy_static::lazy_static;
use proc_macro::TokenStream;
use quote::quote;
use regex_syntax::{
    hir::{
        Anchor, Class, ClassUnicode, ClassUnicodeRange, Hir, HirKind, Literal, Repetition,
        RepetitionKind, RepetitionRange,
    },
    Parser,
};
use std::{
    collections::{hash_map::Entry, HashMap},
    string::ToString,
    sync::RwLock,
};
use syn::parse::Result as SynParseResult;
use syn::{
    parse_macro_input, punctuated::Pair, token::Colon2, BinOp, Error, Expr, ExprLit, 
    Ident, Item, ItemConst, Lit, PathSegment,
};

lazy_static! {
    static ref CRATE_RECS: RwLock<HashMap<String, String>> = RwLock::new(HashMap::new());
}

/// The main regular expression builder.
#[proc_macro_attribute]
pub fn rec(_attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Item::Const(ItemConst { ident, expr, .. }) = parse_macro_input!(item as Item) {
        let re = expr_to_hir(&expr).unwrap().to_string();
        match CRATE_RECS.write().unwrap().entry(ident.to_string()) {
            Entry::Occupied(_) => {
                panic!("User Rec already exists");
            }
            Entry::Vacant(entry) => {
                let _ = entry.insert(re.clone());
            }
        }

        TokenStream::from(quote! {
            const #ident: &str = #re;
        })
    } else {
        panic!("Failed to parse rec attribute");
    }
}

fn expr_to_hir(expr: &Expr) -> SynParseResult<Hir> {
    match expr {
        Expr::Paren(expr) => expr_to_hir(&expr.expr),
        Expr::Lit(expr) => match &expr.lit {
            Lit::Str(literal) => Ok(Hir::concat(
                literal
                    .value()
                    .chars()
                    .map(|c| Hir::literal(Literal::Unicode(c)))
                    .collect(),
            )),
            Lit::Char(literal) => Ok(Hir::literal(Literal::Unicode(literal.value()))),
            _ => Err(Error::new_spanned(expr, "Invalid literal")),
        },
        Expr::Binary(expr) => {
            let lhs = expr_to_hir(&expr.left)?;
            let rhs = expr_to_hir(&expr.right)?;

            match expr.op {
                BinOp::Add(_) => Ok(Hir::concat(vec![lhs, rhs])),
                BinOp::BitOr(_) => {
                    let left_ranges = match lhs.kind() {
                        HirKind::Literal(Literal::Unicode(literal)) => {
                            Some(vec![ClassUnicodeRange::new(*literal, *literal)])
                        }
                        HirKind::Class(Class::Unicode(class)) => Some(class.ranges().to_vec()),
                        _ => None,
                    };
                    let right_ranges = match rhs.kind() {
                        HirKind::Literal(Literal::Unicode(literal)) => {
                            Some(vec![ClassUnicodeRange::new(*literal, *literal)])
                        }
                        HirKind::Class(Class::Unicode(class)) => Some(class.ranges().to_vec()),
                        _ => None,
                    };

                    if let (Some(l), Some(r)) = (left_ranges, right_ranges) {
                        Ok(Hir::class(Class::Unicode(ClassUnicode::new(
                            [l, r].concat(),
                        ))))
                    } else {
                        Ok(Hir::alternation(vec![lhs, rhs]))
                    }
                }
                _ => Err(Error::new_spanned(expr, "Invalid binary op")),
            }
        }
        Expr::Range(expr) => {
            match &expr.from {
                Some(from) => match &expr.to {
                    Some(to) => {
                        if let (HirKind::Literal(Literal::Unicode(start)), HirKind::Literal(Literal::Unicode(end))) = (expr_to_hir(from)?.kind(), expr_to_hir(to)?.kind()) {
                            Ok(Hir::class(Class::Unicode(ClassUnicode::new(vec![
                                ClassUnicodeRange::new(*start, *end),
                            ]))))
                        } else {
                            Err(Error::new_spanned(expr, "Invalid characters for range."))
                        }
                    }
                    None => Err(Error::new_spanned(expr, "No character provided for range end bound.")),
                }
                None => Err(Error::new_spanned(expr, "No character provided for range start bound.")),
            }
        }
        Expr::Repeat(repeat) => {
            let (repeat_expr, greedy) = match repeat.len.deref() {
                Expr::Call(call) => (call.args.first().ok_or_else(|| Error::new_spanned(call, "Lazy repetition requires argument."))?.into_value(), false),
                len => (len, true),
            };

            let kind = match repeat_expr {
                Expr::Lit(literal) => Ok(RepetitionKind::Range(RepetitionRange::Exactly(u32_value(literal)?))),
                Expr::Range(range) => match &range.from {
                    None => match &range.to {
                        None => Ok(RepetitionKind::ZeroOrMore),
                        Some(to) => {
                            match repetition_bound_value(to)? {
                                1 => Ok(RepetitionKind::ZeroOrOne),
                                value => Ok(RepetitionKind::Range(RepetitionRange::Bounded(
                                    0, value,
                                ))),
                            }
                        }
                    },
                    Some(from) => {
                        let from_value = repetition_bound_value(from)?;

                        match &range.to {
                            None => {
                                if from_value == 1 {
                                    Ok(RepetitionKind::OneOrMore)
                                } else {
                                    Ok(RepetitionKind::Range(RepetitionRange::AtLeast(from_value)))
                                }
                            }
                            Some(to) => Ok(RepetitionKind::Range(RepetitionRange::Bounded(
                                from_value,
                                repetition_bound_value(to)?,
                            ))),
                        }
                    }
                },
                _ => Err(Error::new_spanned(repeat_expr, "Invalid repeat expression")),
            }?;

            Ok(Hir::repetition(Repetition {
                hir: Box::new(expr_to_hir(&repeat.expr)?),
                kind,
                greedy,
            }))
        }
        Expr::Path(path) => {
            let segments = &path.path.segments;
            let child = segments
                .last()
                .ok_or_else(|| Error::new_spanned(path, "Path has no segments."))?;
            let parent = segments
                .first()
                .ok_or_else(|| Error::new_spanned(path, "Path has no segments."))?;

            match segment_ident(&parent).to_string().as_str() {
                "anchor" => Ok(Hir::anchor(
                    match segment_ident(&child).to_string().as_str() {
                        "TEXT_START" => Ok(Anchor::StartText),
                        "TEXT_END" => Ok(Anchor::EndText),
                        _ => Err(Error::new_spanned(path, "Invalid anchor path")),
                    }?,
                )),
                "crate" => read_crate_rec(segment_ident(&child)),
                _ => Err(Error::new_spanned(path, "Invalid path")),
            }
        }
        _ => Err(Error::new_spanned(expr, "Invalid expression")),
    }
}

/// Returns the value of `expr` as a [`u32`].
fn repetition_bound_value(expr: &Expr) -> SynParseResult<u32> {
    if let Expr::Lit(literal) = expr {
        u32_value(literal)
    } else {
        Err(Error::new_spanned(expr, "Invalid repetition bound."))
    }
}

/// Returns the value of `literal` as a [`u32`].
fn u32_value(literal: &ExprLit) -> SynParseResult<u32> {
    if let Lit::Int(int) = &literal.lit {
        u32::try_from(int.value()).map_err(|_| Error::new_spanned(literal, "Value is not u32."))
    } else {
        Err(Error::new_spanned(literal, "Invalid literal."))
    }
}

/// Returns the [`Ident`] of `segment`.
fn segment_ident<'a>(segment: &Pair<&'a PathSegment, &Colon2>) -> &'a Ident {
    &segment.value().ident
}

/// Returns the [`Hir`] of the Rec with name `ident` defined in the original crate.
fn read_crate_rec(ident: &Ident) -> SynParseResult<Hir> {
    let crate_recs = CRATE_RECS
        .try_read()
        .map_err(|_| Error::new_spanned(ident, "Error while trying to find Rec in crate."))?;

    match crate_recs.get(&ident.to_string()) {
        Some(crate_rec) => Parser::new()
            .parse(crate_rec)
            .map_err(|_| Error::new_spanned(ident, "Error while re-parsing Rec in crate.")),
        None => Err(Error::new_spanned(ident, "Rec was not found in crate.")),
    }
}

//extern crate alloc;

//pub mod prelude;

//use crate::prelude::{Element, Rec};
//use core::{ops::Deref, str::FromStr};
//use regex::{Captures, Regex};

///// Creates a [`Rec`] representing an [`Element`] that has been assigned a name.
/////
///// # Examples
///// `tkn!` implements the named capture group syntax of `regex`.
///// ```
///// use rec::{prelude::*, tkn};
/////
///// let a_rec = tkn!("digit" => Class::Digit);
/////
///// assert_eq!(a_rec, Rec::from(r"(?P<digit>\d)"))
///// ```
/////
///// [`Pattern`] provides convenient functions for accessing values from tokens.
///// ```
///// use rec::{prelude::*, Pattern, tkn};
/////
///// let pattern = Pattern::new("name: " + tkn!("person" => Class::Any * rpt(1..)));
/////
///// assert_eq!(pattern.name_str("name: Bob", "person"), Some("Bob"));
///// ```
//#[macro_export]
//macro_rules! tkn {
//    ($name:expr => $elmt:expr) => {
//        Rec::from(format!("(?P<{}>{})", $name, $elmt.to_regex()).as_str())
//    };
//}
//
///// A regular expression to be matched against an input string.
//#[derive(Clone, Debug)]
//pub struct Pattern {
//    /// The regular expression.
//    re: Regex,
//}
//
//impl Pattern {
//    /// Creates a new `Pattern`.
//    ///
//    /// This is only safe to use with [`Element`]s that are known prior to runtime. Otherwise, use
//    /// [`str::parse`]
//    ///
//    /// # Panics
//    ///
//    /// Panics if [`Rec`] from `element` is invalid.
//    #[allow(clippy::needless_pass_by_value)] // User interface is simpler when passing by value.
//    pub fn new<T: Element>(element: T) -> Self {
//        Self {
//            re: element.build(),
//        }
//    }
//
//    /// Returns the matched text of the first [`Match`] in `input`.
//    ///
//    /// [`None`] indicates no [`Match`] was found.
//    ///
//    /// # Examples
//    ///
//    /// ```
//    /// use rec::{prelude::*, Pattern};
//    ///
//    /// let pattern = Pattern::new(Class::Digit);
//    ///
//    /// assert_eq!(pattern.find_str("test5"), Some("5"));
//    /// ```
//    pub fn find_str<'t>(&self, input: &'t str) -> Option<&'t str> {
//        self.find(input).map(|mtch| mtch.as_str())
//    }
//
//    /// Returns the first [`Tokens`] found in `input`.
//    ///
//    /// [`None`] indicates no [`Tokens`] was found.
//    ///
//    /// # Examples
//    ///
//    /// Used for accessing multiple [`Match`]es within a single [`Tokens`], without building the
//    /// [`Tokens`] each time. If only accessing the text of a single [`Match`], see [`name_str`].
//    /// ```
//    /// use rec::{tkn, prelude::*, Pattern};
//    ///
//    /// let pattern = Pattern::new(tkn!("field" => Class::Alpha) + ':' + tkn!("value" => Class::Digit));
//    /// let tokens = pattern.tokenize("a:1").unwrap();
//    ///
//    /// assert_eq!(tokens.name_str("field"), Some("a"));
//    /// assert_eq!(tokens.name_str("value"), Some("1"));
//    /// ```
//    pub fn tokenize<'t>(&self, input: &'t str) -> Option<Tokens<'t>> {
//        self.captures(input).map(Tokens::from)
//    }
//
//    /// Returns the matched text with token `name` in the first [`Tokens`] found in `input`.
//    ///
//    /// [`None`] indicates either no [`Tokens`] was found or one was found but it did not contain
//    /// the token `name`.
//    ///
//    /// # Examples
//    ///
//    /// Used for accessing the text of single [`Match`]. If accessing multiple [`Match`]es, see
//    /// [`tokenize`].
//    /// ```
//    /// use rec::{tkn, prelude::*, Pattern};
//    ///
//    /// let pattern = Pattern::new("v:" + tkn!("value" => Class::Digit));
//    ///
//    /// assert_eq!(pattern.name_str("v:4", "value"), Some("4"));
//    /// ```
//    pub fn name_str<'t>(&self, input: &'t str, name: &str) -> Option<&'t str> {
//        self.tokenize(input)
//            .and_then(|tokens| tokens.name_str(name))
//    }
//}
//
//impl Deref for Pattern {
//    type Target = Regex;
//
//    fn deref(&self) -> &Self::Target {
//        &self.re
//    }
//}
//
//impl From<Regex> for Pattern {
//    fn from(other: Regex) -> Self {
//        Self { re: other }
//    }
//}
//
//impl FromStr for Pattern {
//    type Err = regex::Error;
//
//    fn from_str(s: &str) -> Result<Self, Self::Err> {
//        Rec::from(s).try_build().map(Self::from)
//    }
//}
//
///// Stores the matches from named capture groups.
/////
///// `'t` is the lifetime of the input string.
//#[derive(Debug)]
//pub struct Tokens<'t> {
//    /// The matches from named capture groups.
//    captures: Captures<'t>,
//}
//
//impl<'t> Tokens<'t> {
//    /// Returns the matched text with token `name`.
//    ///
//    /// [`None`] indicates no `name` token was found.
//    pub fn name_str(&self, name: &str) -> Option<&'t str> {
//        self.name(name).map(|m| m.as_str())
//    }
//
//    /// Returns the `T` parsed from the matched text with token `name`.
//    ///
//    /// [`None`] indicates no `name` token was found. `Some(Err)` indicates matched text was
//    /// unable to be parsed into `T`.
//    ///
//    /// # Examples
//    ///
//    /// ```
//    /// use rec::{prelude::*, tkn, Pattern};
//    ///
//    /// let pattern = Pattern::new(tkn!("u8" => Class::Digit * rpt(1..)));
//    /// let tokens = pattern.tokenize("42").unwrap();
//    ///
//    /// assert_eq!(tokens.name_parse("u8"), Some(Ok(42)));
//    /// ```
//    pub fn name_parse<T>(&self, name: &str) -> Option<Result<T, <T as FromStr>::Err>>
//    where
//        T: FromStr,
//    {
//        self.name_str(name).map(str::parse::<T>)
//    }
//}
//
//impl<'t> Deref for Tokens<'t> {
//    type Target = Captures<'t>;
//
//    fn deref(&self) -> &Self::Target {
//        &self.captures
//    }
//}
//
//impl<'t> From<Captures<'t>> for Tokens<'t> {
//    fn from(other: Captures<'t>) -> Self {
//        Self { captures: other }
//    }
//}
