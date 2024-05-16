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
    /// Match any alpha numeric character (i.e. `[a-zA-z0-9_]`)
    AlphaNumeric,
    /// Match any within `[...]`
    Within(Vec<char>),
    /// Match any except `[^...]`
    Except(Vec<char>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseError {
    /// Found `\` handing alone
    IncompleteCard,

    /// Found `\c` where `c` is not a known card
    UnknownCard(char),

    /// Found `[` without a closing `]`
    OpenGroupSpecifier,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::IncompleteCard => "flag '\\' isn't followed by any identifier".fmt(f),
            ParseError::UnknownCard(c) => format!("unknown flag identifier {c}").fmt(f),
            ParseError::OpenGroupSpecifier => {
                format!("open group specifiers `[` must be closed with a `]`").fmt(f)
            }
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
        // characters that can be escaped by a backslash `\`
        const ESCAPE: &[char] = &['[', ']', '\\'];

        while let Some(c) = chars.next() {
            match c {
                '\\' => match chars.next() {
                    Some(c) => match c {
                        'd' => tokens.push(AnyDigit),
                        'w' => tokens.push(AlphaNumeric),
                        c if ESCAPE.contains(&c) => tokens.push(Char(c)),
                        c => return Err(UnknownCard(c)),
                    },
                    None => return Err(IncompleteCard),
                },
                '[' => {
                    let specifier = match chars.peek() {
                        Some('^') => {
                            chars.next();
                            Except
                        }
                        Some(_) => Within,
                        None => return Err(OpenGroupSpecifier),
                    };

                    let mut n = 0;
                    let mut group = chars.clone();

                    // look for a closing bracket and store in `n`
                    loop {
                        match group.next() {
                            Some(c) => {
                                match c {
                                    '\\' => match group.next() {
                                        // Two for the `\` and the escaped
                                        Some(c) if ESCAPE.contains(&c) => n += 2,
                                        // All cards lose their power inside the group
                                        _ => return Err(IncompleteCard),
                                    },
                                    c if c != ']' => n += 1,
                                    // `n` is the index of `]`
                                    _ => break,
                                }
                            }
                            None => return Err(OpenGroupSpecifier),
                        }
                    }

                    let mut group = vec![];

                    // collect everything that isn't `]`
                    for _ in 0..n {
                        group.push(chars.next().expect("gauranteed to exist"));
                    }

                    // skipping the `]`
                    chars.next();
                    tokens.push(specifier(group))
                }
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
        let mut j = 0;
        let chars: Vec<char> = input.as_ref().chars().collect();

        while i < token_count && j < chars.len() {
            let c = chars[j];

            match (&self.tokens[i], c) {
                (AnyDigit, d) if d.is_digit(10) => i += 1,
                (AlphaNumeric, w) if w.is_alphanumeric() || w == '_' => i += 1,
                (Char(a), b) if *a == b => i += 1,
                (Within(cs), c) if cs.contains(&c) => i += 1,
                (Except(cs), c) if !cs.contains(&c) => i += 1,
                // the beginning doesn't match
                _ if i == 0 => j += 1,
                // try matching the pattern from the beginning
                _ => {
                    i = 0;
                    continue;
                }
            }

            j += 1;
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

        if self.line_beginning {
            pattern.push('^');
        }

        for token in self.tokens.iter() {
            match token {
                Char(c) => pattern.push(*c),
                AnyDigit => pattern.push_str("\\d"),
                AlphaNumeric => pattern.push_str("\\w"),
                Within(cs) => {
                    pattern.push('[');
                    cs.iter().for_each(|&c| pattern.push(c));
                    pattern.push(']');
                }
                Except(cs) => {
                    pattern.push_str("[^");
                    cs.iter().for_each(|&c| pattern.push(c));
                    pattern.push(']');
                }
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
