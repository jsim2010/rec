use rec::rec;

rec! {char_range_re = 'a'..'z'}

#[test]
fn char_range() {
    assert_eq!(char_range_re(), "[a-z]");
}
