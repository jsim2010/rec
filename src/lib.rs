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

use core::{ops::Deref, convert::TryFrom, result, str::FromStr};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens, TokenStreamExt};
use syn::parse::{Parse, ParseStream, Result};
use syn::{parse_macro_input, BinOp, Error, ExprRepeat, Expr, ExprPath, Ident, ExprLit, Lit, Token};

/// The main regular expression builder.
#[proc_macro]
pub fn rec(item: TokenStream) -> TokenStream {
    let Rec { name, re } = parse_macro_input!(item as Rec);

    TokenStream::from(quote! {
        fn #name() -> String {
            #re.to_string()
        }
    })
}

struct Rec {
    name: Ident,
    re: RegularExpression,
}

impl Parse for Rec {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let name: Ident = input.parse()?;
        let _ = input.parse::<Token![=]>()?;
        let expr: Expr = input.parse()?;

        Ok(Rec { name, re: RegularExpression::try_from(&expr)? })
    }
}

enum RegularExpression {
    Alternation{lhs: Box<RegularExpression>, rhs: Box<RegularExpression>},
    CharacterRanges(CharacterRanges),
    Concatenation{lhs: Box<RegularExpression>, rhs: Box<RegularExpression>},
    Literal(Lit),
    Repeat {
        re: Box<RegularExpression>,
        len: RepeatLen,
        greedy: bool,
    },
    TextLimit(TextLimit),
}

impl RegularExpression {
    fn with_repeat(expr: &ExprRepeat, greedy: bool) -> Result<Self> {
        Ok(RegularExpression::Repeat {
            re: Box::new(RegularExpression::try_from(expr.expr.deref())?),
            len: RepeatLen::try_from(expr.len.deref())?,
            greedy,
        })
    }

    fn character_ranges(&self) -> Option<CharacterRanges> {
        match self {
            RegularExpression::Literal(Lit::Char(literal)) => Some(CharacterRanges{ranges: vec![CharacterRange::with_char(literal.value())]}),
            RegularExpression::CharacterRanges(ranges) => Some(ranges.clone()),
            _ => None,
        }
    }
}

impl TryFrom<&Expr> for RegularExpression {
    type Error = Error;

    fn try_from(expr: &Expr) -> Result<Self> {
        Ok(match expr {
            Expr::Paren(expr) => RegularExpression::try_from(expr.expr.deref())?,
            Expr::Lit(expr) => RegularExpression::Literal(expr.lit.clone()),
            Expr::Binary(expr) => match expr.op {
                BinOp::Add(_) => RegularExpression::Concatenation{
                    lhs: Box::new(RegularExpression::try_from(expr.left.deref())?),
                    rhs: Box::new(RegularExpression::try_from(expr.right.deref())?),
                },
                BinOp::BitOr(_) => {
                    let lhs = RegularExpression::try_from(expr.left.deref())?;
                    let rhs = RegularExpression::try_from(expr.right.deref())?;

                    if let (Some(l), Some(r)) = (lhs.character_ranges(), rhs.character_ranges()) {
                        RegularExpression::CharacterRanges(l.combine(&r))
                    } else {
                        RegularExpression::Alternation {
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        }
                    }
                },
                _ => {
                    return Err(Error::new_spanned(expr, "Invalid BinaryOperation"));
                }
            }
            Expr::Range(expr) => {
                let from = RegularExpression::try_from(expr.from.clone().unwrap().deref())?;
                let to = RegularExpression::try_from(expr.to.clone().unwrap().deref())?;

                if let (RegularExpression::Literal(Lit::Char(start)), RegularExpression::Literal(Lit::Char(end))) = (from, to) {
                    RegularExpression::CharacterRanges(CharacterRanges{ranges: vec![CharacterRange::new(start.value(), end.value())]})
                } else {
                    return Err(Error::new_spanned(expr, "Invalid CharacterRanges"));
                }
            }
            Expr::Path(expr) => RegularExpression::try_from(expr.clone())?,
            Expr::Repeat(expr) => RegularExpression::with_repeat(expr, true)?,
            Expr::Cast(cast) => match cast.expr.deref() {
                Expr::Repeat(expr) => RegularExpression::with_repeat(expr, false)?,
                _ => {
                    return Err(Error::new_spanned(&cast.expr, "Invalid RegularExpression"));
                }
            }
            _ => {
                return Err(Error::new_spanned(expr, "Invalid RegularExpression"));
            }
        })
    }
}

impl TryFrom<ExprPath> for RegularExpression {
    type Error = Error;

    fn try_from(expr: ExprPath) -> Result<Self> {
        let child = expr.path.segments.last().ok_or(Error::new_spanned(&expr, "Empty path"))?.value().ident.to_string();

        match expr.path.segments.first().ok_or(Error::new_spanned(&expr, "Empty path"))?.value().ident.to_string().as_str() {
            "text" => Ok(RegularExpression::TextLimit(child.parse().map_err(|_| Error::new_spanned(&expr, "Invalid TextLimit"))?)),
            _ => Err(Error::new_spanned(expr, "Invalid Part parent")),
        }
    }
}

impl ToTokens for RegularExpression {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let hir = quote! { regex_syntax::hir };
        tokens.append_all(match self {
            RegularExpression::Literal(literal) => match literal {
                Lit::Str(literal) => {
                    let value = literal.value();
                    quote! { #hir::Hir::concat(#value.chars().map(|c| #hir::Hir::literal(#hir::Literal::Unicode(c))).collect()) }
                }
                Lit::Char(literal) => {
                    let value = literal.value();
                    quote! { #hir::Hir::literal(#hir::Literal::Unicode(#value)) }
                }
                _ => quote! { #hir::Hir::empty()},
            }
            RegularExpression::CharacterRanges(ranges) => {
                let (starts, ends) = ranges.split();

                quote! {
                    #hir::Hir::class(
                        #hir::Class::Unicode(
                            #hir::ClassUnicode::new(
                                vec![
                                    #(regex_syntax::hir::ClassUnicodeRange::new(#starts, #ends)),*
                                ]
                            )
                        )
                    )
                }
            }
            RegularExpression::Concatenation{lhs, rhs} => quote! {
                #hir::Hir::concat(vec![#lhs, #rhs])
            },
            RegularExpression::Alternation{lhs, rhs} => {
                quote! {#hir::Hir::alternation(vec![#lhs, #rhs])}
            }
            RegularExpression::TextLimit(text_limit) => quote! {#text_limit},
            RegularExpression::Repeat{re, len, greedy} => quote! {#hir::Hir::repetition(#hir::Repetition{kind: #len, greedy: #greedy, hir: Box::new(#re)})},
        });
    }
}

enum RepeatLen {
    ZeroOrMore,
    ZeroOrOne,
    OneOrMore,
    AtLeast(u32),
    Range(u32, u32),
    Exact(u32),
}

impl TryFrom<&Expr> for RepeatLen {
    type Error = Error;

    fn try_from(expr: &Expr) -> Result<Self> {
        match expr {
            Expr::Lit(literal) => {
                match &literal.lit {
                    Lit::Int(int) => Ok(RepeatLen::Exact(int.value() as u32)),
                    _ => Err(Error::new_spanned(literal, "Invalid RepeatLen")),
                }
            }
            Expr::Range(range) => {
                match &range.from {
                    None => match &range.to {
                        None => Ok(RepeatLen::ZeroOrMore),
                        Some(to) => {
                            if let Expr::Lit(ExprLit{attrs: _, lit: Lit::Int(to_literal)}) = to.deref() {
                                let to_value = to_literal.value() as u32;

                                if to_value == 1 {
                                    Ok(RepeatLen::ZeroOrOne)
                                } else {
                                    Ok(RepeatLen::Range(0, to_value))
                                }
                            } else {
                                Err(Error::new_spanned(to, "Invalid To"))
                            }
                        }
                    },
                    Some(from) => {
                        if let Expr::Lit(ExprLit{attrs: _, lit: Lit::Int(literal)}) = from.deref() {
                            let from_value = literal.value() as u32;

                            match &range.to {
                                None => {
                                    if from_value == 1 {
                                        Ok(RepeatLen::OneOrMore)
                                    } else {
                                        Ok(RepeatLen::AtLeast(from_value))
                                    }
                                }
                                Some(to) => {
                                    if let Expr::Lit(ExprLit{attrs: _, lit: Lit::Int(to_literal)}) = to.deref() {
                                        Ok(RepeatLen::Range(from_value, to_literal.value() as u32))
                                    } else {
                                        Err(Error::new_spanned(from, "Invalid To"))
                                    }
                                }
                            }
                        } else {
                            Err(Error::new_spanned(from, "Invalid From"))
                        }
                    }
                }
            }
            _ => Err(Error::new_spanned(expr, "Invalid RepeatLen")),
        }
    }
}

impl ToTokens for RepeatLen {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let hir = quote! { regex_syntax::hir };

        tokens.append_all(match self {
            RepeatLen::ZeroOrMore => quote!{#hir::RepetitionKind::ZeroOrMore},
            RepeatLen::OneOrMore => quote!{#hir::RepetitionKind::OneOrMore},
            RepeatLen::ZeroOrOne => quote!{#hir::RepetitionKind::ZeroOrOne},
            RepeatLen::AtLeast(min) => quote!{#hir::RepetitionKind::Range(#hir::RepetitionRange::AtLeast(#min))},
            RepeatLen::Range(min, max) => quote!{#hir::RepetitionKind::Range(#hir::RepetitionRange::Bounded(#min, #max))},
            RepeatLen::Exact(value) => quote!{#hir::RepetitionKind::Range(#hir::RepetitionRange::Exactly(#value))},
        });
    }
}

enum TextLimit {
    Start,
    End,
}

impl FromStr for TextLimit {
    type Err = ();

    fn from_str(s: &str) -> result::Result<Self, Self::Err> {
        Ok(match s {
            "START" => TextLimit::Start,
            "END" => TextLimit::End,
            _ => {
                return Err(());
            }
        })
    }
}

impl ToTokens for TextLimit {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let hir = quote! { regex_syntax::hir };

        tokens.append_all(match self {
            TextLimit::Start => quote!{#hir::Hir::anchor(#hir::Anchor::StartText)},
            TextLimit::End => quote!{#hir::Hir::anchor(#hir::Anchor::EndText)},
        });
    }
}

#[derive(Clone, Debug)]
struct CharacterRanges {
    ranges: Vec<CharacterRange>,
}

impl CharacterRanges {
    fn combine(&self, other: &CharacterRanges) -> Self {
        let mut ranges = self.ranges.clone();
        ranges.extend(other.ranges.clone());
        Self {ranges}
    }

    fn split(&self) -> (Vec<char>, Vec<char>) {
        let mut starts = Vec::new();
        let mut ends = Vec::new();

        for range in &self.ranges {
            starts.push(range.start);
            ends.push(range.end);
        }

        (starts, ends)
    }
}

impl FromStr for CharacterRanges {
    type Err = ();

    fn from_str(s: &str) -> result::Result<Self, Self::Err> {
        Ok(CharacterRanges{ ranges:match s {
            "ALPHA" => vec![CharacterRange::new('A', 'Z'), CharacterRange::new('a', 'z')],
            "ANY" => vec![CharacterRange::new('\u{0}', '\u{10ffff}')],
            "DIGIT" => vec![CharacterRange::new('0', '9')],
            "HEX_DIGIT" => vec![CharacterRange::new('0', '9'), CharacterRange::new('A', 'Z'), CharacterRange::new('a', 'z')],
            "NON_ZERO_DIGIT" => vec![CharacterRange::new('1', '9')],
            "SIGN" => vec![CharacterRange::with_char('+'), CharacterRange::with_char('-')],
            "WHITESPACE" => vec![CharacterRange::new('\t', '\n'), CharacterRange::with_char('\r'), CharacterRange::with_char(' ')],
            _ => {
                return Err(());
            }
        }})
    }
}

impl IntoIterator for CharacterRanges {
    type Item = CharacterRange;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.ranges.into_iter()
    }
}

#[derive(Debug, Clone)]
struct CharacterRange {
    start: char,
    end: char,
}

impl CharacterRange {
    fn new(start: char, end: char) -> Self {
        Self {start, end}
    }

    fn with_char(c: char) -> Self {
        Self {start: c, end: c}
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
