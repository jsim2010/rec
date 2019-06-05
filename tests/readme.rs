use std::fs;
use std::process::Command;

#[test]
fn readme_updated() {
    let desired_readme = String::from_utf8_lossy(
        &Command::new("cargo")
            .arg("readme")
            .output()
            .expect("failed to execute command")
            .stdout,
    )
    .into_owned();
    let actual_readme = std::fs::read_to_string("README.md").expect("unable to read 'README.md'");

    assert_eq!(actual_readme, desired_readme);
}
