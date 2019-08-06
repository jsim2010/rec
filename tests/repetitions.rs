use rec::rec;

rec! {zero_or_more_re = ['x'; ..]}
rec! {lazy_zero_or_more_re = ['x'; ..] as lazy}
rec! {one_or_more_re = ['x'; 1..]}
rec! {lazy_one_or_more_re = ['x'; 1..] as lazy}
rec! {zero_or_one_re = ['x'; ..=1]}
rec! {lazy_zero_or_one_re = ['x'; ..=1] as lazy}
rec! {at_least_re = ['x'; 2..]}
rec! {lazy_at_least_re = ['x'; 2..] as lazy}
rec! {range_re = ['x'; 3..=5]}
rec! {lazy_range_re = ['x'; 3..=5] as lazy}
rec! {at_most_re = ['x'; ..=4]}
rec! {lazy_at_most_re = ['x'; ..=4] as lazy}
rec! {exact_re = ['x'; 3]}

#[test]
fn repeat_zero_or_more() {
    assert_eq!(zero_or_more_re(), "x*");
}

#[test]
fn lazy_repeat_zero_or_more() {
    assert_eq!(lazy_zero_or_more_re(), "x*?");
}

#[test]
fn repeat_one_or_more() {
    assert_eq!(one_or_more_re(), "x+");
}

#[test]
fn lazy_repeat_one_or_more() {
    assert_eq!(lazy_one_or_more_re(), "x+?");
}

#[test]
fn repeat_zero_or_one() {
    assert_eq!(zero_or_one_re(), "x?");
}

#[test]
fn lazy_repeat_zero_or_one() {
    assert_eq!(lazy_zero_or_one_re(), "x??");
}

#[test]
fn repeat_at_least_and_at_most() {
    assert_eq!(range_re(), "x{3,5}");
}

#[test]
fn lazy_repeat_at_least_and_at_most() {
    assert_eq!(lazy_range_re(), "x{3,5}?");
}

#[test]
fn repeat_at_least() {
    assert_eq!(at_least_re(), "x{2,}");
}

#[test]
fn lazy_repeat_at_least() {
    assert_eq!(lazy_at_least_re(), "x{2,}?");
}

#[test]
fn repeat_at_most() {
    assert_eq!(at_most_re(), "x{0,4}");
}

#[test]
fn lazy_repeat_at_most() {
    assert_eq!(lazy_at_most_re(), "x{0,4}?");
}

#[test]
fn repeat_exact() {
    assert_eq!(exact_re(), "x{3}");
}
