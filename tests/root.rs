use version_sync::assert_markdown_deps_updated;

/// The crate version listed in the README file shall match the current version.
#[test]
fn readme_deps_updated() {
    assert_markdown_deps_updated!("README.md");
}
