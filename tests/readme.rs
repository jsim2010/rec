use std::fs;
use std::process::Command;

#[test]
fn readme_updated() {
    let actual_readme = fs::read_to_string("README.md").expect("unable to read 'README.md'");
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
