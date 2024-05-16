use std::{
    env::args,
    error::Error,
    fmt::{self, Display},
    io::stdin,
    process::exit,
    str::FromStr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Pattern {
    tokens: Vec<PatternToken>,
}

/// Regex Pattern tokens
#[derive(Debug, Clone, PartialEq, Eq)]
enum PatternToken {
    /// Match literal character
    Char(char),
    /// Match any digit
    AnyDigit,
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseError {
    IncompleteCard,
    UnknownCard(char),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::IncompleteCard => "flag '\\' isn't followed by any identifier".fmt(f),
            ParseError::UnknownCard(c) => format!("unknown flag identifier {c}").fmt(f),
        }
    }
}

impl Error for ParseError {}

impl FromStr for Pattern {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl Pattern {
    fn parse<S: AsRef<str>>(source: S) -> Result<Self, ParseError> {
        use ParseError::*;
        use PatternToken::*;

        let mut chars = source.as_ref().chars().peekable();
        let mut tokens: Vec<PatternToken> = vec![];

        while let Some(c) = chars.next() {
            match c {
                '\\' => match chars.next() {
                    Some(c) => match c {
                        'd' => tokens.push(AnyDigit),
                        '\\' => tokens.push(Char('\\')),
                        c => return Err(UnknownCard(c)),
                    },
                    None => return Err(IncompleteCard),
                },
                c => tokens.push(Char(c)),
            }
        }

        Ok(Self { tokens })
    }

    /// Determine if an input matches this pattern.
    fn matches<S: AsRef<str>>(&self, input: S) -> bool {
        use PatternToken::*;

        let token_count = self.tokens.len();
        let mut i = 0;
        let mut chars = input.as_ref().chars();

        while let Some(c) = chars.next() {
            // all tokens have been consumed
            if i >= token_count {
                break;
            }

            match (&self.tokens[i], c) {
                (AnyDigit, d) if d.is_digit(10) => i += 1,
                (Char(a), b) if *a == b => i += 1,
                _ => i = 0,
            }
        }

        // there are some pattern tokens that haven't been consumed, thus the input doesn't match
        // the pattern
        if i < token_count {
            false
        // all tokens have been consumed, thus the input matches the pattern
        } else {
            true
        }
    }
}

impl Display for Pattern {
    /// Display the original source of the pattern
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PatternToken::*;

        let mut pattern = String::new();
        for token in self.tokens.iter() {
            match token {
                Char(c) => pattern.push(*c),
                AnyDigit => pattern.push_str("\\d"),
            }
        }

        pattern.fmt(f)
    }
}

fn main() -> anyhow::Result<()> {
    let mut args = args();
    args.next();

    if args.next() != Some("-E".into()) {
        println!("Expected first argument to be '-E'");
        exit(1);
    }

    let Some(pattern) = args.next() else {
        println!("Missing regex pattern");
        exit(1)
    };

    let pattern = Pattern::from_str(&pattern)?;

    let mut input_line = String::new();

    stdin().read_line(&mut input_line)?;

    if !pattern.matches(&input_line) {
        exit(1)
    }

    Ok(())
}
