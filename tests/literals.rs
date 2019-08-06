use rec::rec;

rec! {char_re = 'a'}
rec! {str_re = "test"}

#[test]
fn char() {
    assert_eq!(char_re(), "a");
}

#[test]
fn str() {
    assert_eq!(str_re(), "test");
}
