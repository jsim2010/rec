use std::{fs, process::Command};
use version_sync::assert_markdown_deps_updated;

/// The name of the program shall be "rec".
#[test]
fn name() {
    #[allow(unused_imports)] // Test only needs to confirm that library with correct name exists.
    use rec;
}

/// [`rec`] shall be used as a library that provides the following:
///     1) "rec" = an attribute procedural macro that can be applied to a constant item with type [`&str`]. The procedural macro defines a constant [`&str`] with the given identifier.
#[test]
fn interface() {
    use rec::rec;

    #[rec]
    const TEST: &str = ' ';

    /// Assert TEST is const &str.
    const _: &str = TEST;
}

/// The README.md shall match the crate documentation.
#[test]
fn readme() {
    let actual_readme = fs::read_to_string("README.md")
        .expect("unable to read 'README.md'")
        .replace('\r', "");
    let desired_readme = String::from_utf8_lossy(
        &Command::new("cargo")
            .arg("readme")
            .output()
            .expect("failed to execute command")
            .stdout,
    )
    .into_owned();

    assert_eq!(actual_readme, desired_readme);
}

/// The crate version listed in the README file shall match the current version.
#[test]
fn readme_deps_updated() {
    assert_markdown_deps_updated!("README.md");
}
