use rec::rec;

rec! {single_char_or_re = 'a' | 'z'}
rec! {multiple_char_or_re = 'a' | 'x' | 'z'}
rec! {multiple_range_char_re = 'a' | 'b' | 'c'}
rec! {range_or_char_re = ('0'..'9') | 'a'}
rec! {char_or_range_re = 'a' | ('0'..'9')}
rec! {char_or_str_re = 'a' | "xyz"}
rec! {str_or_range_re = "abc" | ('x'..'z')}

#[test]
fn single_char_or() {
    assert_eq!(single_char_or_re(), "[az]");
}

#[test]
fn multiple_char_or() {
    assert_eq!(multiple_char_or_re(), "[axz]");
}

#[test]
fn range_or_char() {
    assert_eq!(range_or_char_re(), "[0-9a]");
}

#[test]
fn char_or_range() {
    assert_eq!(char_or_range_re(), "[0-9a]");
}

#[test]
fn multiple_range_char() {
    assert_eq!(multiple_range_char_re(), "[a-c]");
}

#[test]
fn char_or_str() {
    assert_eq!(char_or_str_re(), r"a|xyz");
}

#[test]
fn str_or_range() {
    assert_eq!(str_or_range_re(), r"abc|[x-z]");
}
