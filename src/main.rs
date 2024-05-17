use std::{
    env::args,
    error::Error,
    fmt::{self, Display},
    io::stdin,
    process::exit,
    str::FromStr,
};

/// Characters that can be escaped by a backslash `\`
const ESCAPE: &[char] = &['[', ']', '\\', '$', '+', '*', '?', '.'];

#[derive(Debug, Clone, PartialEq, Eq)]
struct Pattern {
    tokens: Vec<PatternToken>,
}

/// Regex Pattern tokens
#[derive(Debug, Clone, PartialEq, Eq)]
enum PatternToken {
    /// Match literal character
    Char(char),
    /// Match any digit `\d`
    AnyDigit,
    /// Match anything `.`
    Any,
    /// Match any alpha numeric character (i.e. `[a-zA-z0-9_]`)
    AlphaNumeric,
    /// Match any within `[...]`
    Within(Vec<char>),
    /// Match any except `[^...]`
    Except(Vec<char>),
    /// Match line beginning, corresponds to `^` at the beginning of the pattern.
    LineBeginning,
    /// Match line ending, corresponds to `$` at the end of the pattern.
    LineEnding,
    /// Match the embedded `pattern` accroding to the specified range.
    Quantifier {
        /// The minimum amount the pattern should be repeated for.
        min: usize,
        /// The maximum amount the pattern should be repeated for.
        max: usize,
        /// The pattern being quantified.
        inner: Box<Pattern>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseError {
    /// Found `\` handing alone
    IncompleteCard,

    /// Found `\c` where `c` is not a known card
    UnknownCard(char),

    /// Found `[` without a closing `]`
    OpenGroupSpecifier,

    /// A [`quantifier`][PatternToken::Quantifier] doesn't hold a pattern
    EmptyQuantifier {
        /// The string representation found in the source
        repr: String,
    },
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::IncompleteCard => "flag '\\' isn't followed by any identifier".fmt(f),
            ParseError::UnknownCard(c) => format!("unknown flag identifier {c}").fmt(f),
            ParseError::OpenGroupSpecifier => {
                "open group specifiers `[` must be closed with a `]`".fmt(f)
            }
            ParseError::EmptyQuantifier { repr } => {
                format!("quantifier `{repr}` doesn't hold an expression").fmt(f)
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

        if let Some(&'^') = chars.peek() {
            chars.next();
            tokens.push(LineBeginning);
        }

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
                c @ ('+' | '*' | '?') => {
                    let (min, max) = match c {
                        '*' => (0, usize::MAX),
                        '+' => (1, usize::MAX),
                        '?' => (0, 1),
                        c => unreachable!("quantifier {c} should've been match"),
                    };

                    match tokens.pop() {
                        Some(token) => tokens.push(Quantifier {
                            min,
                            max,
                            inner: Box::new(Pattern {
                                tokens: vec![token],
                            }),
                        }),
                        None => return Err(EmptyQuantifier { repr: c.into() }),
                    }
                }
                '.' => tokens.push(Any),
                '$' if chars.peek().is_none() => tokens.push(LineEnding),
                c => tokens.push(Char(c)),
            }
        }

        Ok(Self { tokens })
    }
}

impl Display for Pattern {
    /// Display the original source of the pattern
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for token in self.tokens.iter() {
            token.fmt(f)?;
        }
        Ok(())
    }
}

impl Display for PatternToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PatternToken::*;
        match self {
            Char(c) => {
                if ESCAPE.contains(c) {
                    '\\'.fmt(f)?;
                }
                c.fmt(f)
            }
            Any => '.'.fmt(f),
            AnyDigit => "\\d".fmt(f),
            AlphaNumeric => "\\w".fmt(f),
            Within(cs) => {
                '['.fmt(f)?;
                for c in cs.iter() {
                    c.fmt(f)?;
                }
                ']'.fmt(f)
            }
            Except(cs) => {
                "[^".fmt(f)?;
                for c in cs.iter() {
                    c.fmt(f)?;
                }
                ']'.fmt(f)
            }
            LineBeginning => '^'.fmt(f),
            LineEnding => '$'.fmt(f),
            Quantifier { min, max, inner } => {
                inner.to_string().fmt(f)?;
                match (*min, *max) {
                    (0, usize::MAX) => '*'.fmt(f),
                    (1, usize::MAX) => '+'.fmt(f),
                    (0, 1) => '?'.fmt(f),
                    (a, b) if a == b => format!("{{{a}}}").fmt(f),
                    (a, usize::MAX) => format!("{{{a},}}").fmt(f),
                    (a, b) => format!("{{{a},{b}}}").fmt(f),
                }
            }
        }
    }
}

struct SliceDisplay<'a, T: 'a>(&'a [T]);

impl<'a, T: fmt::Display + 'a> fmt::Display for SliceDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for item in self.0 {
            write!(f, "{item}")?;
        }
        Ok(())
    }
}

/// Determine if an input matches this pattern. The output corresponds to the index at which the
/// `pattern` have been consumed (i.e. matched)
fn matches<P: AsRef<[PatternToken]>, S: AsRef<[char]>>(pattern: P, input: S) -> Option<usize> {
    use PatternToken::*;

    let tokens = pattern.as_ref();
    let token_count = tokens.len();
    let mut i = 0;
    let mut j = 0;
    let chars = input.as_ref();
    let char_count = chars.len();

    #[cfg(feature = "verbose")]
    {
        println!(
            "\nMatching '{}' against {:?}",
            SliceDisplay(&tokens),
            input.as_ref().iter().collect::<String>()
        );
        println!("0 <= i < {token_count}, 0 <= j < {char_count}");
        println!("");
    }

    if let Some(LineBeginning) = tokens.first() {
        i += 1;
    }

    while i < token_count && j < char_count {
        let c = chars[j];
        let token = &tokens[i];

        #[cfg(feature = "verbose")]
        print!("tokens[{i}], chars[{j}]\t");
        match (&token, c) {
            (Any, _) => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {c:?}");
                i += 1;
            }
            (AnyDigit, d) if d.is_digit(10) => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {d:?}");
                i += 1
            }
            (AlphaNumeric, w) if w.is_alphanumeric() || w == '_' => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {w:?}");
                i += 1
            }
            (Char(a), b) if *a == b => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {b:?}");
                i += 1
            }
            (Within(cs), c) if cs.contains(&c) => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {c:?}");
                i += 1
            }
            (Except(cs), c) if !cs.contains(&c) => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> {c:?}");
                i += 1
            }
            (LineBeginning | LineEnding, '\n') => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=> '\\n'");
                i += 1
            }
            (LineEnding, '\r') if chars.get(j + 1).map(|&c| c == '\n').unwrap_or(false) => {
                #[cfg(feature = "verbose")]
                println!("{token:?} <=>  '\\r\\n'");
                i += 1;
                j += 1; // accounting for the '\r'
            }
            (Quantifier { min, max, inner }, _) => {
                let (min, max) = (*min, *max);
                // do the minimum requirement
                let mut k = j;
                let mut fail = false;

                for _ in 0..min {
                    let Some(m) = matches(inner.as_ref(), &chars[k..]) else {
                        fail = true;
                        break;
                    };

                    k += m;
                }

                if fail {
                    if i == 0 {
                        j += 1;
                        continue;
                    }
                    i = 0;
                    continue;
                }

                // the rest of the tokens (a.k.a. epsilon transition)
                let rest = &tokens[i + 1..];

                for _ in min..max {
                    if let Some(m) = matches(rest, &chars[k..]) {
                        // achieved the minimum requirements and the rest of the tokens match
                        return Some(m);
                    }
                    let Some(m) = matches(inner.as_ref(), &chars[k..]) else {
                        fail = true;
                        break;
                    };

                    k += m;
                }
                if fail {
                    if i == 0 {
                        j += 1;
                        continue;
                    }
                    i = 0;
                    continue;
                }
                j = k;
            }
            // the beginning doesn't match
            _ if i == 0 => {
                #[cfg(feature = "verbose")]
                println!("advancing...");
                j += 1
            }
            // try matching the pattern from the beginning
            _ => {
                #[cfg(feature = "verbose")]
                println!("trying pattern beginning");
                i = 0;
                continue;
            }
        }

        j += 1;
    }

    let consumed_tokens = i >= token_count;

    if consumed_tokens {
        #[cfg(feature = "verbose")]
        println!("MATCH");
        Some(j)
    } else {
        #[cfg(feature = "verbose")]
        println!("NO MATCH");
        None
    }
}

impl AsRef<Pattern> for Pattern {
    fn as_ref(&self) -> &Pattern {
        self
    }
}

impl AsRef<[PatternToken]> for Pattern {
    fn as_ref(&self) -> &[PatternToken] {
        &self.tokens
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

    #[cfg(feature = "verbose")]
    {
        println!("");
        println!("pattern tokens:  {pattern:?}");
        println!("pattern display: {pattern}");
        println!("input:           {input_line:?}");
        println!("");
    }

    if matches(pattern.tokens, input_line.chars().collect::<Vec<char>>()).is_none() {
        exit(1)
    }

    Ok(())
}
