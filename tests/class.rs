use rec::prelude::*;

#[test]
fn alpha() {
    assert_eq!(Class::Alpha, Rec::from("[[:alpha:]]"));
}

#[test]
fn alpha_num() {
    assert_eq!(Class::AlphaNum, Rec::from("[[:alnum:]]"));
}

#[test]
fn digit() {
    assert_eq!(Class::Digit, Rec::from(r"\d"));
}

#[test]
fn whitespace() {
    assert_eq!(Class::Whitespace, Rec::from(r"\s"));
}

#[test]
fn any() {
    assert_eq!(Class::Any, Rec::from("."));
}

#[test]
fn start() {
    assert_eq!(Class::Start, Rec::from("^"));
}

#[test]
fn end() {
    assert_eq!(Class::End, Rec::from("$"));
}

#[test]
fn sign() {
    assert_eq!(Class::Sign, Rec::from(r"[+\-]"));
}

#[test]
fn non_zero_digit() {
    assert_eq!(Class::NonZeroDigit, Rec::from(r"[1-9]"));
}

#[test]
fn hex_digit() {
    assert_eq!(Class::HexDigit, Rec::from("[[:xdigit:]]"));
}

#[test]
fn union_with_atom() {
    assert_eq!(Class::Alpha | '0', Rec::from("[[:alpha:]0]"));
    assert_eq!(
        Class::Alpha | Ch::AnyOf("12345"),
        Rec::from("[[:alpha:]12345]")
    );
}

#[test]
fn alternate_with_element() {
    assert_eq!(Class::Digit | String::from("abc"), Rec::from(r"\d|abc"));
    assert_eq!(Class::HexDigit | "def", Rec::from("[[:xdigit:]]|def"));
    assert_eq!(Class::Whitespace | Rec::from("test"), Rec::from(r"\s|test"));
}

#[test]
fn alternate_after_element() {
    assert_eq!(String::from("abc") | Class::Digit, Rec::from(r"abc|\d"));
    assert_eq!("xyz" | Class::Digit, Rec::from(r"xyz|\d"));
    assert_eq!(Rec::from("test") | Class::Digit, Rec::from(r"test|\d"));
}
