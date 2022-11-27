use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::process::Command;

#[test]
fn should_accept_short_version() {
    version("-v").unwrap();
}

#[test]
fn should_accept_long_version() {
    version("--version").unwrap();
}

#[test]
fn simple() {
    expect_output(&["1 2 +"], "3").unwrap();
    expect_output(&["1", "2", "+"], "3").unwrap();
    expect_output(&["2 3 x"], "6").unwrap();
    expect_output(&["1", "2", "s"], "4").unwrap();
}

fn version(arg: &str) -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("rpn").expect("to find rpn binary");
    cmd.arg(arg);
    cmd.assert()
        .success()
        .try_stdout(predicate::str::contains("rpn"))?;
    Ok(())
}

fn expect_output(args: &[&str], expected: &str) -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("rpn").expect("to find rpn binary");
    let formatted: &str = &format!("{expected}\n");
    cmd.args(args);
    cmd.assert()
        .success()
        .try_stdout(predicate::eq(formatted))?;
    Ok(())
}
