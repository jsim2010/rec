# rec

Regular Expression Constructor - making regular expressions fun

`rec` is a Rust library that simplifies the process of writing, reading, and using regular
expressions. This library is intended for all users working with regular expressions, no matter
their familiarity with regular expression syntax. Below is a summary of the functionality
provided by `rec`:

- WYSIWYG: &str is interpreted exactly as written (i.e. no metacharacters); all metacharacters
(as well as other useful patterns) are provided by the [`ChCls`] enum.
- Simple to understand quantifier syntax and capture name syntax.
- Uses operators to provide easy to understand expressions.
- [`Pattern`] returns exactly what is requested to reduce boilerplate.

This library utilizes the [`regex`] crate.

## Getting Started

Add the following to your `Cargo.toml`:

```toml
[dependencies]
rec = "0.4.0"
```

## Examples
### Create a Regex
If you prefer API of [`regex`], you can use a [`Rec`] to construct a [`Regex`].
```rust
use rec::{some};
use rec::ChCls::{Digit, Whitespace};

let a_rec = "hello" + some(Whitespace) + (Digit | "world");
let regex = a_rec.build();

assert!(regex.is_match("hello    world"));
```

### Use Pattern to tokenize
Instead of using [`Regex`], you can use [`Pattern`] to handle basic matching needs.
```rust
use rec::{some, tkn, var, Element, Pattern};
use rec::ChCls::Digit;

let decimal_number = Pattern::new(tkn!(some(Digit) => "whole") + "." + var(Digit));

assert_eq!(decimal_number.tokenize("23.2").get("whole"), Some("23"));
```

## FAQ

### I know regular expression syntax; why should I use `rec`?

In order for code to be easily maintainable, it should be as simple as possible. Even if the
original developer understands their regular expression, it is beneficial for the project as a
whole if all contributors are able to easily understand the function of a regular expression.

[`ChCls`]: enum.ChCls.html
[`Rec`]: struct.Rec.html
[`Pattern`]: struct.Pattern.html

License: MIT
