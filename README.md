# rec

Regular Expression Constructor - the recreational version of regular expressions

`rec` is a Rust library that simplifies the process of writing, reading, and using regular
expressions. This library is intended for all users working with regular expressions, no matter
their familiarity with regular expression syntax. Below is a summary of the functionality
provided by `rec`:

- WYSIWYG: [`&str`] is interpreted exactly as written (i.e. no metacharacters); all metacharacters
(as well as other useful patterns) are provided by the [`Ch`] struct.
- Simple to understand quantifier and capture group syntaxes.
- Uses operators to provide easy to understand expressions.
- [`Pattern`] expands on [`Regex`] API to simplify access to data.

This library utilizes the [`regex`] crate.

## Getting Started

Add the following to your `Cargo.toml`:

```toml
[dependencies]
rec = "0.8.0"
```

## Examples
### Use Regex API.
A [`Pattern`] is a smart pointer to a [`Regex`], so one can call the same functions.
```rust
use rec::{some, Ch, Pattern};

let pattern = Pattern::new("hello" + some(Ch::whitespace()) + (Ch::digit() | "world"));

assert!(pattern.is_match("hello    world"));
```

### Use Pattern to capture a group.
[`Pattern`] additionally provides helper functions to reduce boilerplate.
```rust
use rec::{some, tkn, var, Element, Pattern};
use rec::Ch;

let decimal_number = Pattern::new(tkn!("whole" => some(Ch::digit())) + "." + var(Ch::digit()));

assert_eq!(decimal_number.name_str("23.2", "whole"), Some("23"));
```

## FAQ

### I know regular expression syntax; why should I use `rec`?

In order for code to be easily maintainable, it should be as simple as possible. Even if the
original developer understands their regular expression, it is beneficial for the project as a
whole if all contributors are able to easily understand the function of a regular expression.

License: MIT
