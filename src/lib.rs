//! Regular Expression Constructor - the recreational version of regular expressions
//!
//! `rec` is a Rust library that simplifies the process of reading and writing regular expressions.
//! This library is intended for all users working with regular expressions, no matter their
//! familiarity with regular expression syntax. Below is a summary of the functionality provided by
//! `rec`:
//!
//! - WYSIWYG: [`&str`] and [`char`] are interpreted exactly as written (i.e. no metacharacters);
//! - Uses operators from rust language syntax to provide easy to understand expressions.
//! - Declares regular expressions as const [`&str`] values that are valid with the [`regex`]
//! crate.
//!
//! # Getting Started
//!
//! Add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rec = "0.11.0"
//! ```
//!
//! # Examples
//! ```
//! use rec::rec;
//! use regex::Regex;
//!
//! #[rec]
//! const HELLO_WORLD: &str = "hello" + [' '; 1..] + "world";
//!
//! let re = Regex::new(HELLO_WORLD).unwrap();
//! assert!(re.is_match("hello    world"));
//! ```
//!
//! Alternation is implemented by `|`.
//!
//! ```
//! use rec::rec;
//! use regex::Regex;
//!
//! #[rec]
//! const VERSION: &str = "debug" | "release";
//!
//! let re = Regex::new(VERSION).unwrap();
//! assert!(re.is_match("release"));
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
#![no_std]

extern crate alloc;
extern crate proc_macro;

use alloc::{boxed::Box, string::ToString, vec};
use core::{
    convert::{TryFrom, TryInto},
    ops::Deref,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use regex_syntax::hir::{
    Class, ClassUnicode, ClassUnicodeRange, Group, GroupKind, Hir, HirKind, Literal, Repetition,
    RepetitionKind, RepetitionRange,
};
use syn::{
    parse::{Parse, ParseStream, Result as SynParseResult},
    parse_macro_input, BinOp, Error, Expr, ExprBinary, ExprLit, ExprPath, ExprRange, ExprRepeat,
    ExprUnary, Ident, Item, ItemConst, Lit, Path, UnOp,
};

/// The main regular expression builder.
#[proc_macro_attribute]
pub fn rec(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let Rec { ident, re } = parse_macro_input!(item as Rec);

    TokenStream::from(quote! {
        const #ident: &str = #re;
    })
}

/// A regular expression.
enum Re {
    /// A regular expression represented by a [`Hir`].
    Const(Hir),
    /// A regular expression stored in a variable.
    Variable(Path),
}

impl Re {
    /// Returns an [`Re`] that alternates `other` with `self`.
    fn alternate(self, other: Self) -> Self {
        if let (Some(mut self_class), Some(other_class)) = (self.class(), other.class()) {
            self_class.union(&other_class);
            Re::Const(Hir::class(Class::Unicode(self_class)))
        } else {
            match (self, other) {
                (Re::Const(self_hir), Re::Const(other_hir)) => {
                    Re::Const(Hir::alternation(vec![self_hir, other_hir]))
                }
                (_, _) => Re::Const(Hir::empty()),
            }
        }
    }

    /// Returns an [`Re`] that concatentates `other` on `self`.
    fn concat(self, other: Self) -> Self {
        match (self, other) {
            (Re::Const(self_hir), Re::Const(other_hir)) => Re::Const(Hir::concat(vec![
                lump_for_concatenation(self_hir),
                lump_for_concatenation(other_hir),
            ])),
            (_, _) => Re::Const(Hir::empty()),
        }
    }

    /// Returns an [`Re`] that intersects `self` and `other`.
    ///
    /// [`Err`] indicates either `self` or `other` are unable to intersect.
    fn intersect(self, other: &Self) -> Result<Self, ()> {
        if let (Some(mut self_class), Some(other_class)) = (self.class(), other.class()) {
            self_class.intersect(&other_class);
            Ok(Re::Const(Hir::class(Class::Unicode(self_class))))
        } else {
            Err(())
        }
    }

    /// Returns an [`Re`] that repeats `self` as defined by `kind` and `greedy`.
    fn repeat(self, kind: RepetitionKind, greedy: bool) -> Self {
        match self {
            Re::Const(hir) => Re::Const(Hir::repetition(Repetition {
                // Hir::repetition does not correctly handle the case where hir is a "compound" expression.
                hir: Box::new(lump_for_repetition(hir)),
                kind,
                greedy,
            })),
            Re::Variable(path) => Re::Variable(path),
        }
    }

    /// Returns the [`ClassUnicode`] that represents `self`.
    ///
    /// [`None`] indicates `self` is not able to be represented by a [`ClassUnicode`].
    fn class(&self) -> Option<ClassUnicode> {
        match self {
            Re::Const(hir) => match hir.kind() {
                HirKind::Literal(Literal::Unicode(literal)) => {
                    Some(ClassUnicode::new(vec![ClassUnicodeRange::new(
                        *literal, *literal,
                    )]))
                }
                HirKind::Class(Class::Unicode(class)) => Some(class.clone()),
                _ => None,
            },
            _ => None,
        }
    }
}

impl TryFrom<Expr> for Re {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        match value {
            Expr::Lit(expr) => expr.lit.try_into(),
            Expr::Range(expr) => expr.try_into(),
            Expr::Paren(expr) => (*expr.expr).try_into(),
            Expr::Repeat(expr) => expr.try_into(),
            Expr::Unary(expr) => expr.try_into(),
            Expr::Binary(expr) => expr.try_into(),
            Expr::Path(expr) => expr.try_into(),
            Expr::Box(..)
            | Expr::InPlace(..)
            | Expr::Array(..)
            | Expr::Call(..)
            | Expr::MethodCall(..)
            | Expr::Tuple(..)
            | Expr::Cast(..)
            | Expr::Type(..)
            | Expr::Let(..)
            | Expr::If(..)
            | Expr::While(..)
            | Expr::ForLoop(..)
            | Expr::Loop(..)
            | Expr::Match(..)
            | Expr::Closure(..)
            | Expr::Unsafe(..)
            | Expr::Block(..)
            | Expr::Assign(..)
            | Expr::AssignOp(..)
            | Expr::Field(..)
            | Expr::Index(..)
            | Expr::Reference(..)
            | Expr::Break(..)
            | Expr::Continue(..)
            | Expr::Return(..)
            | Expr::Macro(..)
            | Expr::Struct(..)
            | Expr::Group(..)
            | Expr::Try(..)
            | Expr::Async(..)
            | Expr::TryBlock(..)
            | Expr::Yield(..)
            | Expr::Verbatim(..) => Err(Error::new_spanned(value, "Invalid expression")),
        }
    }
}

impl TryFrom<ExprBinary> for Re {
    type Error = Error;

    fn try_from(value: ExprBinary) -> Result<Self, Self::Error> {
        let expr = value.clone();
        let lhs: Self = (*value.left).try_into()?;
        let rhs: Self = (*value.right).try_into()?;

        match value.op {
            BinOp::Add(..) => Ok(lhs.concat(rhs)),
            BinOp::BitOr(..) => Ok(lhs.alternate(rhs)),
            BinOp::BitAnd(..) => lhs
                .intersect(&rhs)
                .map_err(|_| Error::new_spanned(expr, "Can only intersect 2 classes")),
            BinOp::Sub(..)
            | BinOp::Mul(..)
            | BinOp::Div(..)
            | BinOp::Rem(..)
            | BinOp::And(..)
            | BinOp::Or(..)
            | BinOp::BitXor(..)
            | BinOp::Shl(..)
            | BinOp::Shr(..)
            | BinOp::Eq(..)
            | BinOp::Lt(..)
            | BinOp::Le(..)
            | BinOp::Ne(..)
            | BinOp::Ge(..)
            | BinOp::Gt(..)
            | BinOp::AddEq(..)
            | BinOp::SubEq(..)
            | BinOp::MulEq(..)
            | BinOp::DivEq(..)
            | BinOp::RemEq(..)
            | BinOp::BitXorEq(..)
            | BinOp::BitAndEq(..)
            | BinOp::BitOrEq(..)
            | BinOp::ShlEq(..)
            | BinOp::ShrEq(..) => Err(Error::new_spanned(value.op, "Invalid binary op")),
        }
    }
}

impl TryFrom<ExprPath> for Re {
    type Error = Error;

    fn try_from(value: ExprPath) -> Result<Self, Self::Error> {
        Ok(Re::Variable(value.path))
    }
}

impl TryFrom<ExprRange> for Re {
    type Error = Error;

    fn try_from(value: ExprRange) -> Result<Self, Self::Error> {
        match (&value.from, &value.to) {
            (Some(from), Some(to)) => Ok(Re::Const(Hir::class(Class::Unicode(ClassUnicode::new(
                vec![ClassUnicodeRange::new(
                    char_from_expr(from.deref())?,
                    char_from_expr(to.deref())?,
                )],
            ))))),
            (None, _) => Err(Error::new_spanned(value, "Expected starting range bound")),
            (_, None) => Err(Error::new_spanned(value, "Expected ending range bound")),
        }
    }
}

impl TryFrom<ExprRepeat> for Re {
    type Error = Error;

    fn try_from(value: ExprRepeat) -> Result<Self, Self::Error> {
        let (repeat_expr, greedy) = match value.len.deref() {
            Expr::Call(ref call) => (
                call.args
                    .first()
                    .ok_or_else(|| {
                        Error::new_spanned(call, "Expected argument to specify repeition")
                    })?
                    .into_value(),
                false,
            ),
            len => (len, true),
        };

        (*value.expr)
            .try_into()
            .and_then(|re: Self| Ok(re.repeat(repetition_kind_from_expr(repeat_expr)?, greedy)))
    }
}

impl TryFrom<ExprUnary> for Re {
    type Error = Error;

    fn try_from(value: ExprUnary) -> Result<Self, Self::Error> {
        match value.op {
            UnOp::Not(..) => {
                let expr = value.expr.clone();

                if let Some(mut class) = Self::try_from(*value.expr)?.class() {
                    class.negate();
                    Ok(Re::Const(Hir::class(Class::Unicode(class))))
                } else {
                    Err(Error::new_spanned(
                        &expr,
                        "Invalid expression after negation.",
                    ))
                }
            }
            UnOp::Deref(..) | UnOp::Neg(..) => {
                Err(Error::new_spanned(value, "Invalid unary operator."))
            }
        }
    }
}

impl TryFrom<Lit> for Re {
    type Error = Error;

    fn try_from(value: Lit) -> Result<Self, Self::Error> {
        match value {
            Lit::Str(literal) => Ok(Hir::concat(
                literal
                    .value()
                    .chars()
                    .map(|c| Hir::literal(Literal::Unicode(c)))
                    .collect(),
            )),
            Lit::Char(literal) => Ok(Hir::literal(Literal::Unicode(literal.value()))),
            Lit::ByteStr(..)
            | Lit::Byte(..)
            | Lit::Int(..)
            | Lit::Float(..)
            | Lit::Bool(..)
            | Lit::Verbatim(..) => Err(Error::new_spanned(value, "Invalid literal")),
        }
        .map(Re::Const)
    }
}

impl ToTokens for Re {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Re::Const(hir) => hir.to_string().to_tokens(tokens),
            Re::Variable(path) => path.to_tokens(tokens),
        }
    }
}

/// Constructs a regular expression.
struct Rec {
    /// The identifier.
    ident: Ident,
    /// The regular expression.
    re: Re,
}

impl Parse for Rec {
    fn parse(input: ParseStream<'_>) -> SynParseResult<Self> {
        if let Item::Const(ItemConst { ident, expr, .. }) = input.parse().map(Item::Const)? {
            Ok(Self {
                ident,
                re: (*expr).try_into()?,
            })
        } else {
            Err(input.error("Rec must be a const item"))
        }
    }
}

/// Converts an [`Expr`] to a [`RepetitionKind`].
fn repetition_kind_from_expr(expr: &Expr) -> SynParseResult<RepetitionKind> {
    match expr {
        Expr::Lit(literal) => Ok(RepetitionKind::Range(RepetitionRange::Exactly(
            u32_from_literal(literal)?,
        ))),
        Expr::Range(range) => match &range.from {
            None => match &range.to {
                None => Ok(RepetitionKind::ZeroOrMore),
                Some(to) => match u32_from_expr(to)? {
                    1 => Ok(RepetitionKind::ZeroOrOne),
                    value => Ok(RepetitionKind::Range(RepetitionRange::Bounded(0, value))),
                },
            },
            Some(from) => {
                let from_value = u32_from_expr(from)?;

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
                        u32_from_expr(to)?,
                    ))),
                }
            }
        },
        _ => Err(Error::new_spanned(
            expr,
            "Expected expression representing repetition",
        )),
    }
}

/// Converts an [`Expr`] to a [`char`].
fn char_from_expr(expr: &Expr) -> SynParseResult<char> {
    match expr {
        Expr::Lit(expr) => match &expr.lit {
            Lit::Char(literal) => Ok(literal.value()),
            _ => Err(Error::new_spanned(expr, "Expected `char`")),
        },
        _ => Err(Error::new_spanned(expr, "Expected `char`")),
    }
}

/// Returns a [`Hir`] that is a valid representation of `hir` as a [`Hir::Repetition`] element.
fn lump_for_repetition(hir: Hir) -> Hir {
    match hir.kind() {
        HirKind::Concat(..) | HirKind::Alternation(..) => group_hir(hir),
        _ => hir,
    }
}

/// Returns a [`Hir`] that is a valid representation of `hir` as a [`Hir::Concat`] element.
fn lump_for_concatenation(hir: Hir) -> Hir {
    match hir.kind() {
        HirKind::Alternation(..) => group_hir(hir),
        _ => hir,
    }
}

/// Returns a [`Hir`] that wraps `hir` in a non-capturing group.
fn group_hir(hir: Hir) -> Hir {
    Hir::group(Group {
        kind: GroupKind::NonCapturing,
        hir: Box::new(hir),
    })
}

/// Converts an [`Expr`] to a [`u32`].
fn u32_from_expr(expr: &Expr) -> SynParseResult<u32> {
    if let Expr::Lit(literal) = expr {
        u32_from_literal(literal)
    } else {
        Err(Error::new_spanned(expr, "Expected u32 literal"))
    }
}

/// Converts a [`ExprLit`] to a [`u32`].
fn u32_from_literal(literal: &ExprLit) -> SynParseResult<u32> {
    if let Lit::Int(int) = &literal.lit {
        u32::try_from(int.value()).map_err(|_| Error::new_spanned(literal, "Expected u32 literal"))
    } else {
        Err(Error::new_spanned(literal, "Expected u32 literal"))
    }
}
