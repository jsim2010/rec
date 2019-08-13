# rec

Regular Expression Constructor - the recreational version of regular expressions

`rec` is a Rust library that simplifies the process of reading and writing regular expressions.
This library is intended for all users working with regular expressions, no matter their
familiarity with regular expression syntax. Below is a summary of the functionality provided by
`rec`:

- WYSIWYG: [`&str`] and [`char`] are interpreted exactly as written (i.e. no metacharacters);
- Uses operators from rust language syntax to provide easy to understand expressions.
- Declares regular expressions as const [`&str`] values that are valid with the [`regex`]
crate.

## Getting Started

Add the following to your `Cargo.toml`:

```toml
[dependencies]
rec = "0.11.0"
```

## Examples
```rust
use rec::rec;
use regex::Regex;

#[rec]
const HELLO_WORLD: &str = "hello" + [' '; 1..] + "world";

let re = Regex::new(HELLO_WORLD).unwrap();
assert!(re.is_match("hello    world"));
```

Alternation is implemented by `|`.

```rust
use rec::rec;
use regex::Regex;

#[rec]
const VERSION: &str = "debug" | "release";

let re = Regex::new(VERSION).unwrap();
assert!(re.is_match("release"));
```

## FAQ

### I know regular expression syntax; why should I use `rec`?

In order for code to be easily maintainable, it should be as simple as possible. Even if the
original developer understands their regular expression, it is beneficial for the project as a
whole if all contributors are able to easily understand the function of a regular expression.

License: MIT
