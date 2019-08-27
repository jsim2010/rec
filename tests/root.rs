use std::{fs, process::Command};
use version_sync::assert_markdown_deps_updated;

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
