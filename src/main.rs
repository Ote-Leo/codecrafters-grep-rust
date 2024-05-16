use std::env;
use std::io::stdin;
use std::process::exit;

fn match_pattern(input_line: &str, pattern: &str) -> bool {
    if pattern.chars().count() == 1 {
        return input_line.contains(pattern);
    } else {
        panic!("Unhandled pattern: {}", pattern)
    }
}

fn main() -> anyhow::Result<()> {
    if env::args().nth(1).unwrap() != "-E" {
        println!("Expected first argument to be '-E'");
        exit(1);
    }

    let pattern = env::args().nth(2).unwrap();
    let mut input_line = String::new();

    stdin().read_line(&mut input_line)?;

    if !match_pattern(&input_line, &pattern) {
        exit(1)
    }

    Ok(())
}
