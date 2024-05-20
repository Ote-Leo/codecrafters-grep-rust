use std::{
    collections::HashMap, env::args, error::Error, fmt::{self, Display}, io::stdin, process::exit, str::FromStr
};

/// Characters that can be escaped by a backslash `\`
const ESCAPE: &[char] = &['[', ']', '\\', '$', '+', '*', '?', '.', '(', ')', '|'];
#[cfg(feature = "verbose")]
const INDENTATION: &str = "    ";

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
    /// Match the embedded [`Pattern`] accroding to the specified range.
    Quantifier {
        /// The minimum amount the pattern should be repeated for.
        min: usize,
        /// The maximum amount the pattern should be repeated for.
        max: usize,
        /// The pattern being quantified.
        inner: Box<Pattern>,
    },
    /// A sequence of [`Pattern`]s to alternative between using `|` (e.g. `(p1|p2|...|pn)`)
    Group {
        /// A reference identifier used by [`backreferences`]
        ///
        /// [`backreferences`]: PatternToken::BackReference
        reference: usize,
        /// The inner sequence of patterns
        inner: Vec<Pattern>,
    },
    /// A back-reference to a [`group`] (i.e. it must follow it); represented as `\<index>`.
    ///
    /// [`group`]: PatternToken::Group
    BackReference {
        /// A one-based index.
        index: usize,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseError {
    /// Found `\` handing alone
    IncompleteCard,

    /// Found `\c` where `c` is not a known card
    UnknownCard(char),

    /// Found an unblanaced `[]`, `{}`, or `()`
    UnbalancedSepcifier { open: char, close: char },

    /// A [`quantifier`][PatternToken::Quantifier] doesn't hold a pattern
    EmptyQuantifier {
        /// The string representation found in the source
        repr: String,
    },
    /// A [`backreference`][PatternToken::BackReference] has an non-positive integer index
    InvalidBackreference(usize),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ParseError::*;
        match self {
            IncompleteCard => "flag '\\' isn't followed by any identifier".fmt(f),
            UnknownCard(c) => format!("unknown flag identifier {c}").fmt(f),
            UnbalancedSepcifier { open, close } => {
                format!("open group specifiers `{open}` must be closed with a `{close}`").fmt(f)
            }
            EmptyQuantifier { repr } => {
                format!("quantifier `{repr}` doesn't hold an expression").fmt(f)
            }
            InvalidBackreference(index) => {
                format!("back-references must be a positive integer, but found {index}").fmt(f)
            }
        }
    }
}

impl Error for ParseError {}


impl Pattern {
    fn parse<S: AsRef<str>>(
        source: S,
        references: &mut Vec<usize>,
        reference_count: &mut usize,
        #[cfg(feature = "verbose")] depth: usize,
    ) -> Result<Self, ParseError> {
        use ParseError::*;
        use PatternToken::*;

        #[cfg(feature = "verbose")]
        let indentation = [INDENTATION].repeat(depth).join("");

        let mut chars = source.as_ref().chars().peekable();
        let mut tokens: Vec<PatternToken> = vec![];

        if let Some(&'^') = chars.peek() {
            #[cfg(feature = "verbose")]
            println!("{indentation}LineBeginning <=> '^'");
            chars.next();
            tokens.push(LineBeginning);
        }

        while let Some(c) = chars.next() {
            match c {
                '\\' => {
                    let token = match chars.next() {
                        Some(c) => match c {
                            'd' => AnyDigit,
                            'w' => AlphaNumeric,
                            c if ESCAPE.contains(&c) => Char(c),
                            c if c.is_ascii_digit() => {
                                let mut buf = String::from(c);
                                while let Some(&d) = chars.peek() {
                                    if d.is_ascii_digit() {
                                        buf.push(d);
                                        chars.next();
                                    } else {
                                        break
                                    }
                                }
                                let index = usize::from_str(&buf).expect(&format!("huge backreference {buf}"));
                                // TODO: adding index validation
                                if index < 1 {
                                    return Err(InvalidBackreference(index));
                                }
                                references.push(index);
                                BackReference { index }
                            }
                            c => return Err(UnknownCard(c)),
                        },
                        None => return Err(IncompleteCard),
                    };

                    #[cfg(feature = "verbose")]
                    println!("{indentation}{token:?} <=> '{token}'");

                    tokens.push(token)
                }
                '[' => {
                    let specifier = match chars.peek() {
                        Some('^') => {
                            chars.next();
                            Except
                        }
                        Some(_) => Within,
                            None => return Err(UnbalancedSepcifier { open: '[', close: ']' }),
                    };

                    let n;
                    let mut group = chars.clone().enumerate();

                    // look for a closing bracket and store in `n`
                    loop {
                        match group.next() {
                            Some((i, c)) => {
                                match c {
                                    '\\' => match group.next() {
                                        Some((_, c)) if ESCAPE.contains(&c) => (),
                                        _ => return Err(IncompleteCard),
                                    },
                                    // `n` is the index of `]`
                                    ']' => {
                                        n = i;
                                        break
                                    }
                                    _ => (),
                                }
                            }
                            None => return Err(UnbalancedSepcifier { open: '[', close: ']' }),
                        }
                    }

                    let mut group = vec![];

                    // collect everything that isn't `]`
                    for _ in 0..n {
                        group.push(chars.next().expect("guaranteed to exist"));
                    }

                    chars.next(); // skipping the `]`
                    tokens.push(specifier(group))
                }
                '{' => todo!("handle the case of parsing quantifiers, also you might need to update the error message of OpenGroupSpecifier"),
                '(' => {
                    let mut n = 0;
                    let mut group = chars.clone().enumerate();
                    let mut group_indecies = vec![];

                    let mut brackets = vec!['('];

                    // look for a closing bracket and store in `n`
                    loop {
                        if brackets.is_empty() {
                            break;
                        }

                        let Some((i, c)) = group.next() else {
                            return Err(UnbalancedSepcifier { open: '(', close: ')' });
                        };

                        match c {
                            '\\' => match group.next() {
                                Some((_, c)) if ESCAPE.contains(&c) => (),
                                Some((_, 'd' | 'w')) => (),
                                _ => return Err(IncompleteCard),
                            },
                            c @ ( '['| '('| '{' ) => brackets.push(c),
                            c @ ( ']'| ')'| '}' ) => {
                                let open = match c {
                                    ']' => '[',
                                    ')' => '(',
                                    '}' => '{',
                                    _ => unreachable!(),
                                };

                                match brackets.pop() {
                                    Some(bracket) if bracket == open => {
                                        if brackets.is_empty() {
                                            n = i;
                                        }
                                    },
                                    _ => return Err(UnbalancedSepcifier { open, close: c }),
                                }
                            }
                            '|' if brackets.len() == 1 => {
                                group_indecies.push(i);
                            }
                            _ => (),
                        }
                    }

                    let mut inner = vec![];

                    #[cfg(feature = "verbose")]
                    println!("{indentation}PARSING ALTERNATIVES:");
                    let reference = *reference_count + 1;
                    *reference_count += 1;

                    let mut v = 0;
                    for g in group_indecies {
                        let mut p = String::new();
                        for _ in v..g {
                            p.push(chars.next().expect("guaranteed to exist"));
                            v += 1;
                        }

                        #[cfg(feature = "verbose")]
                        {
                            println!("{indentation}PARSING INNER PATTERN {p:?}:");
                            inner.push(Pattern::parse(&p, references, reference_count, depth + 1)?);
                        }

                        #[cfg(not(feature = "verbose"))]
                        inner.push(Pattern::parse(&p, references, reference_count)?);

                        chars.next(); // skipping the `|`
                            v += 1;
                    }

                    // collect everything that isn't `)`
                    {
                        let mut p = String::new();
                        for _ in v..n {
                            p.push(chars.next().expect("guaranteed to exist"));
                        }

                        #[cfg(feature = "verbose")]
                        {
                            println!("{indentation}PARSING INNER PATTERN {p:?}:");
                            inner.push(Pattern::parse(&p, references, reference_count, depth + 1)?);
                        }
                        #[cfg(not(feature = "verbose"))]
                        inner.push(Pattern::parse(&p, references, reference_count)?);
                    }

                    chars.next(); // skipping the `)`
                    tokens.push(Group { inner, reference });
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
                            inner: {
                                let previous_token = vec![token];
                                #[cfg(feature = "verbose")]
                                {
                                    let ts = previous_token.iter().map(|t| t.to_string()).collect::<Vec<_>>().join("");
                                    println!("{indentation}Quantifying {ts} <=> {c:?}");
                                }

                                Box::new(Pattern { tokens: previous_token })
                            }
                        }),
                        None => return Err(EmptyQuantifier { repr: c.into() }),
                    }
                }
                '.' => {
                    #[cfg(feature = "verbose")]
                    println!("{indentation}LineEnding <=> {c:?}");
                    tokens.push(Any)
                }
                '$' if chars.peek().is_none() => {
                    #[cfg(feature = "verbose")]
                    println!("{indentation}LineEnding <=> {c:?}");
                    tokens.push(LineEnding)
                }
                c => {
                    #[cfg(feature = "verbose")]
                    println!("{indentation}Char({c:?}) <=> {c:?}");
                    tokens.push(Char(c))
                } 
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
            Group { reference: _, inner } => {
                '('.fmt(f)?;
                inner
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<String>>()
                    .join("|")
                    .fmt(f)?;
                ')'.fmt(f)
            }
            BackReference { index } => {
                '\\'.fmt(f)?;
                index.fmt(f)
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
fn matches<P: AsRef<[PatternToken]>, S: AsRef<[char]>>(pattern: P, input: S, references: &[usize]) -> Option<usize> {
    #[cfg(feature = "verbose")]
    { match_loop(pattern, input, true, references, &mut HashMap::new(), 1) }
    #[cfg(not(feature = "verbose"))]
    { match_loop(pattern, input, true, references, &mut HashMap::new()) }
}

fn match_loop<P: AsRef<[PatternToken]>, S: AsRef<[char]>>(
    pattern: P,
    input: S,
    advance: bool,
    requested_references: &[usize],
    captured_references: &mut HashMap<usize, String>,
    #[cfg(feature = "verbose")] depth: usize,
) -> Option<usize> {
    use PatternToken::*;

    #[cfg(feature = "verbose")]
    let indentation = [INDENTATION].repeat(depth).join("");

    let tokens = pattern.as_ref();
    let chars = input.as_ref();
    let token_count = tokens.len();
    let char_count = chars.len();
    let mut i = 0;
    let mut j = 0;

    macro_rules! failure_advance {
        () => {
            if i == 0 { j += 1; continue; } else { i = 0; continue; }
        };
    }

    #[cfg(feature = "verbose")]
    {
        println!(
            "\n{indentation}Matching '{}' against {:?}",
            SliceDisplay(&tokens),
            input.as_ref().iter().collect::<String>()
        );
        println!("{indentation}0 <= i < {token_count}, 0 <= j < {char_count}");
        println!("");
    }

    if let Some(LineBeginning) = tokens.first() {
        i += 1;
    }

    // storing the last point of failure to backtrack to
    let mut last_failure = 0;

    while i < token_count && j < char_count {
        let c = chars[j];
        let token = &tokens[i];

        #[cfg(feature = "verbose")]
        let indentation = format!("{indentation}tokens[{i}], chars[{j}]\t");
        match (&token, c) {
            (Any, _) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {c:?}");
                i += 1;
            }
            (AnyDigit, d) if d.is_digit(10) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {d:?}");
                i += 1
            }
            (AlphaNumeric, w) if w.is_alphanumeric() || w == '_' => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {w:?}");
                i += 1
            }
            (Char(a), b) if *a == b => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {b:?}");
                i += 1
            }
            (Within(cs), c) if cs.contains(&c) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {c:?}");
                i += 1
            }
            (Except(cs), c) if !cs.contains(&c) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> {c:?}");
                i += 1
            }
            (LineBeginning | LineEnding, '\n') => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=> '\\n'");
                i += 1
            }
            (LineEnding, '\r') if chars.get(j + 1).map(|&c| c == '\n').unwrap_or(false) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{token:?} <=>  '\\r\\n'");
                i += 1;
                j += 1; // accounting for the '\r'
            }
            (Quantifier { min, max, inner }, _) => {
                let (min, max) = (*min, *max);
                // do the minimum requirement
                let mut k = j;
                let mut fail = false;

                for _ in 0..min {
                    let _match = {
                        #[cfg(feature = "verbose")]
                        {
                            match_loop(inner.as_ref(), &chars[k..], false, requested_references, captured_references, depth + 1)
                        }
                        #[cfg(not(feature = "verbose"))]
                        { match_loop(inner.as_ref(), &chars[k..], false, requested_references, captured_references) }
                    };
                    let Some(m) = _match else {
                        fail = true;
                        break;
                    };

                    k += m;
                }

                if fail {
                    failure_advance!();
                }

                // the rest of the tokens (a.k.a. epsilon transition)
                let rest = &tokens[i + 1..];

                // NOTE: innser pattern must be greedy
                // (i.e. capture as much as possible then pop-backtrack)

                let mut widths = vec![];
                for _ in 0..max {
                    if k > char_count {
                        break;
                    }

                    let _match = {
                        #[cfg(feature = "verbose")]
                        { match_loop(inner.as_ref(), &chars[k..], false, requested_references, captured_references, depth + 1) }
                        #[cfg(not(feature = "verbose"))]
                        { match_loop(inner.as_ref(), &chars[k..], false, requested_references, captured_references) }
                    };

                    if let Some(m) = _match {
                        widths.push(m);
                        k += m;
                    } else {
                        break;
                    };
                }
                widths.push(0);

                for w in widths.into_iter().rev() {
                    k -= w;
                    let _match = {
                        #[cfg(feature = "verbose")]
                        { match_loop(rest, &chars[k..], false, requested_references, captured_references, depth + 1) }
                        #[cfg(not(feature = "verbose"))]
                        { match_loop(rest, &chars[k..], false, requested_references, captured_references) }
                    };

                    if let Some(m) = _match {
                        // achieved the minimum requirements and the rest of the tokens match
                        return Some(k + m);
                    }
                }

                failure_advance!();
            }
            (Group { reference, inner }, _) => {
                let mut k = j;
                let mut any_match = false;
                for inner_pattern in inner.iter() {

                    let _match =  {
                        #[cfg(feature = "verbose")]
                        { match_loop(inner_pattern, &chars[k..], false, requested_references, captured_references, depth + 1) }
                        #[cfg(not(feature = "verbose"))]
                        { match_loop(inner_pattern, &chars[k..], false, requested_references, captured_references) }
                    };

                    if let Some(m) = _match {
                        any_match = true;
                        k += m;
                        break;
                    }
                }

                if any_match {
                    if requested_references.contains(reference) {
                        let captured_reference = chars[j..k].iter().collect::<String>();
                        #[cfg(feature = "verbose")]
                        println!("{indentation}CAPTURED: ({reference}, {captured_reference:?})");
                        *captured_references.entry(*reference).or_default() = captured_reference;
                    }

                    i += 1;
                    j = k;
                    continue;
                } else {
                    failure_advance!();
                }
            }
            (BackReference { index }, _) if captured_references.contains_key(index) => {
                let capture = &captured_references[index];
                let capture_len = capture.len();

                if capture_len > char_count {
                    failure_advance!();
                }

                let mut capture_chars = capture.chars();
                let mut k = j;
                let mut match_capture = true;
                while let Some(c) = capture_chars.next() {
                    if c != chars[k] {
                        match_capture = false;
                        break;
                    }
                    k += 1;
                }

                if !match_capture {
                    #[cfg(feature = "verbose")]
                    println!("{indentation} Mismatch BackReference ({index}, {capture:?})");
                    failure_advance!();
                }
                #[cfg(feature = "verbose")]
                println!("{indentation} Match BackReference ({index}, {capture:?})");
                i += 1;
                j = k - 1;
            }
            (_t, _c) if !advance => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{_t:?} <!=> {_c:?}, NO MATCH - early exiting.");
                return None;
            }
            // the beginning doesn't match
            (_t, _c) if i == 0 => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{_t:?} <!=> {_c:?}, advancing...");
            }
            // try matching the pattern from the beginning
            (_t, _c) => {
                #[cfg(feature = "verbose")]
                println!("{indentation}{_t:?} <!=> {_c:?}, trying pattern beginning");
                last_failure += 1;
                j = last_failure;
                i = 0;
                continue;
            }
        }

        j += 1;
    }

    let consumed_input = j >= char_count;
    let consumed_tokens = i >= token_count;

    if consumed_input && !consumed_tokens && tokens[i] == LineEnding {
        return Some(j);
    }

    if consumed_tokens {
        #[cfg(feature = "verbose")]
        println!("{indentation}MATCH");
        Some(j)
    } else {
        #[cfg(feature = "verbose")]
        println!("{indentation}NO MATCH");
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

    let mut references = vec![];
    let mut reference_count = 0;
    #[cfg(feature = "verbose")]
    let pattern = Pattern::parse(&pattern, &mut references, &mut reference_count, 1)?;
    #[cfg(not(feature = "verbose"))]
    let pattern = Pattern::parse(&pattern, &mut references, &mut reference_count)?;

    let mut input_line = String::new();

    stdin().read_line(&mut input_line)?;

    #[cfg(feature = "verbose")]
    {
        println!("");
        println!("requested backrefereces:  {references:?}");
        println!("pattern tokens:           {pattern:#?}");
        println!("pattern display:          {pattern}");
        println!("input:                    {input_line:?}");
        println!("");
    }

    if matches(pattern.tokens, input_line.chars().collect::<Vec<char>>(), &references).is_none() {
        exit(1)
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! succ {
        ($pattern: literal, $($case: literal),*) => {
            let mut references = vec![];
            let mut reference_count = 0;
            let pattern = Pattern::parse($pattern, &mut references, &mut reference_count).unwrap();
            $(
                assert!(matches(&pattern, $case.chars().collect::<Vec<_>>(), &references).is_some());
            )*
        };
    }

    macro_rules! fail {
        ($pattern: literal, $($case: literal),*) => {
            let mut references = vec![];
            let mut reference_count = 0;
            let pattern = Pattern::parse($pattern, &mut references, &mut reference_count).unwrap();
            $(
                assert!(matches(&pattern, $case.chars().collect::<Vec<_>>(), &references).is_none());
            )*
        };
    }

    #[test]
    fn single_backreferences() {
        succ!(r"(cat) and \1", "cat and cat");
        fail!(r"(cat) and \1", "cat and dog");
        succ!(r"(\w\w\w\w \d\d\d) is doing \1 times", "grep 101 is doing grep 101 times");
        fail!(r"(\w\w\w \d\d\d) is doing \1 times", "$?! 101 is doing $?! 101 times");
        fail!(r"(\w\w\w\w \d\d\d) is doing \1 times", "grep yes is doing grep yes times");
        succ!(r"([abcd]+) is \1, not [^xyz]+", "abcd is abcd, not efg");
        fail!(r"([abcd]+) is \1, not [^xyz]+", "efgh is efgh, not efg");
        fail!(r"([abcd]+) is \1, not [^xyz]+", "abcd is abcd, not xyz");
        succ!(r"^(\w+) starts and ends with \1$", "this starts and ends with this");
        fail!(r"^(this) starts and ends with \1$", "that starts and ends with this");
        fail!(r"^(this) starts and ends with \1$", "this starts and ends with this?");
        succ!(r"once a (drea+mer), alwaysz? a \1", "once a dreaaamer, always a dreaaamer");
        fail!(r"once a (drea+mer), alwaysz? a \1", "once a dremer, always a dreaaamer");
        fail!(r"once a (drea+mer), alwaysz? a \1", "once a dreaaamer, alwayszzz a dreaaamer");
        succ!(r"(b..s|c..e) here and \1 there", "bugs here and bugs there");
        fail!(r"(b..s|c..e) here and \1 there", "bugz here and bugs there");
    }

    #[test]
    fn alternation() {
        succ!("a (cat|dog)", "a cat", "a dog");
        fail!("a (cat|dog)", "a cow");
    }

    #[test]
    fn wild_card() {
        succ!("c.t", "cat", "cot");
        fail!("c.t", "car");
    }

    #[test]
    fn option_quantifier() {
        succ!("ca?t", "cat", "act");
        fail!("ca?t", "dog", "cag");
    }

    #[test]
    fn at_least_once_quantifier() {
        succ!("ca+t", "caaats", "cat");
        fail!("ca+t", "act");
    }

    #[test]
    fn line_ending() {
        succ!("cat$", "cat", "ccat");
        fail!("cat$", "cats");
    }

    #[test]
    fn line_beginning() {
        succ!("^log", "log", "logg");
        fail!("^log", "slog");
    }

    #[test]
    fn token_combination() {
        succ!(r"\d apple", "sally has 3 apples", "sally has 32 apples");
        fail!(r"\d apple", "sally has 1 orange");

        succ!(
            r"\d\d\d apple",
            "sally has 123 apples",
            "sally has 1234 apples"
        );
        fail!(r"\d\\d\\d apple", "sally has 12 apples");

        succ!(r"\d \w\w\ws", "sally has 3 dogs", "sally has 4 dogs");
        fail!(r"\d \w\w\ws", "sally has 1 dog");
    }

    #[test]
    fn negative_character_groups() {
        succ!("[^xyz]", "apple");
        fail!("[^anb]", "banana");
    }

    #[test]
    fn positive_character_groups() {
        succ!("[abcd]", "a");
        fail!("[abcd]", "efgh");
    }

    #[test]
    fn alphanumeric() {
        succ!(r"\w", "word");
        fail!(r"\w", "$!?");
    }

    #[test]
    fn digits() {
        succ!(r"\d", "123");
        fail!(r"\d", "apple");
    }

    #[test]
    fn literals() {
        succ!("d", "dog");
        fail!("f", "dog");
    }
}
