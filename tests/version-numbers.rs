use version_sync::assert_markdown_deps_updated;

#[test]
fn readme_deps_updated() {
    assert_markdown_deps_updated!("README.md");
}
