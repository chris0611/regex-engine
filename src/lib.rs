use std::{collections::HashSet, iter::Peekable};

type CharacterRange = std::ops::RangeInclusive<char>;

#[derive(Debug, Clone)]
pub enum Pattern {
    Empty,                               // Empty pattern that matches everything
    Literal(char),                       // A single character, e.g. 'a'
    Dot,                                 // Matches any single character
    Sequence(Box<Sequence>),             // A sequence of patterns, e.g. "a*(c)?"
    Alternation(Box<Alternation>),       // Alternation, e.g. "a|b"
    Group(Box<Pattern>),                 // Grouping, e.g. "(abc)"
    CharacterClass(Box<CharacterClass>), // Character class, e.g. "[a-z]"
    Repetition(Box<Repetition>),         // Repetition, e.g. "a*", "a?" or "a{2,4}"
}

impl Pattern {
    pub fn sequence(e: Sequence) -> Pattern {
        Pattern::Sequence(Box::new(e))
    }

    pub fn alternation(e: Alternation) -> Pattern {
        Pattern::Alternation(Box::new(e))
    }

    pub fn character_class(e: CharacterClass) -> Pattern {
        Pattern::CharacterClass(Box::new(e))
    }

    pub fn repetition(e: Repetition) -> Pattern {
        Pattern::Repetition(Box::new(e))
    }
}

#[derive(Debug, Clone)]
pub struct Sequence {
    pub patterns: Vec<Pattern>,
}

impl Sequence {
    pub fn into_pattern(mut self) -> Pattern {
        match self.patterns.len() {
            0 => Pattern::Literal(' '), // TODO: Fix with Pattern::Empty once implemented
            1 => self.patterns.pop().unwrap(),
            _ => Pattern::sequence(self),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Alternation {
    pub patterns: Vec<Pattern>,
}

impl Alternation {
    pub fn into_pattern(mut self) -> Pattern {
        match self.patterns.len() {
            0 => Pattern::Empty,
            1 => self.patterns.pop().unwrap(),
            _ => Pattern::alternation(self),
        }
    }
}

#[derive(Debug, Clone)]
pub struct CharacterClass {
    pub ranges: Vec<CharacterRange>,
    pub negated: bool,
}

#[derive(Debug, Clone)]
pub struct Repetition {
    pub pattern: Box<Pattern>,
    pub kind: RepetitionKind,
    pub greedy: bool, // TODO: Lazy matching
}

#[derive(Debug, Clone)]
pub enum RepetitionKind {
    ZeroOrMore, // Zero or more repetitions, e.g. "a*"
    OneOrMore,  // One or more repetitions, e.g. "a+"
    Optional,   // Optional pattern, e.g. "a?"
    Range(Option<usize>, Option<usize>),
}

//=== Matching logic ===

pub fn match_pattern(pattern: &str, input: &str) -> Result<bool, String> {
    let mut chars = pattern.chars().peekable();
    let parsed = parse_pattern(&mut chars)?;

    if chars.peek().is_some() {
        // Return error with remaining characters
        return Err(format!(
            "Unexpected characters after pattern: {}",
            chars.collect::<String>()
        ));
    }

    println!("{:#?}", parsed);
    let result = matches(&parsed, input);
    Ok(result.contains(&""))
}

// Matches the string against the pattern and returns all possible
// suffixes that can be matched by the pattern
// If the pattern matches the entire string, it returns an empty string
fn matches<'a>(pat: &Pattern, input: &'a str) -> Vec<&'a str> {
    match pat {
        Pattern::Empty => vec![input],
        Pattern::Literal(c) => {
            let mut chars = input.chars();
            match chars.next() {
                Some(first) if first == *c => {
                    vec![chars.as_str()]
                }
                _ => vec![],
            }
        }
        Pattern::Dot => {
            let mut chars = input.chars();
            if chars.next().is_some() {
                return vec![chars.as_str()];
            }
            vec![]
        }
        Pattern::Sequence(seq) => match_sequence(&seq.patterns, input),
        Pattern::Alternation(alt) => {
            let mut results = vec![];
            for option in &alt.patterns {
                results.extend(matches(option, input));
            }
            results
        }
        Pattern::Group(inner) => matches(inner, input),
        Pattern::CharacterClass(class) => {
            if let Some(c) = input.chars().next() {
                let matched = class.ranges.iter().any(|r| r.contains(&c));
                if matched != class.negated {
                    return vec![&input[c.len_utf8()..]];
                }
            }
            vec![]
        }
        Pattern::Repetition(repetition) => {
            let (min, max) = match repetition.kind {
                RepetitionKind::ZeroOrMore => (0, usize::MAX),
                RepetitionKind::OneOrMore => (1, usize::MAX),
                RepetitionKind::Optional => (0, 1),
                RepetitionKind::Range(min, max) => (min.unwrap_or(0), max.unwrap_or(usize::MAX)),
            };

            let mut results = HashSet::new();
            let mut stack = vec![(input, 0)];

            while let Some((remaining, count)) = stack.pop() {
                if count >= min && !results.contains(&remaining) {
                    results.insert(remaining);
                }

                if count < max {
                    for suffix in matches(&repetition.pattern, remaining) {
                        stack.push((suffix, count + 1));
                    }
                }
            }

            results.into_iter().collect()
        }
    }
}

fn match_sequence<'a>(seq: &[Pattern], input: &'a str) -> Vec<&'a str> {
    let mut suffixes = vec![input];
    for part in seq {
        let mut next_suffixes = Vec::new();
        for s in suffixes {
            next_suffixes.extend(matches(part, s));
        }
        suffixes = next_suffixes;
        if suffixes.is_empty() {
            break;
        }
    }
    suffixes
}

//=== Parsing logic ===

// pattern = term ('|' term)*
fn parse_pattern(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    let mut alternates = vec![];

    // First term
    if let Some('|') = chars.peek() {
        alternates.push(Pattern::Empty);
    } else if let Ok(term) = parse_term(chars) {
        alternates.push(term);
    }

    while let Some('|') = chars.peek() {
        chars.next(); // Consume '|'
        if let Some('|') = chars.peek() {
            alternates.push(Pattern::Empty);
            chars.next(); // Consume '|'
        } else if chars.peek().is_none() {
            alternates.push(Pattern::Empty);
            break;
        } else if let Ok(term) = parse_term(chars) {
            alternates.push(term);
        } else {
            alternates.push(Pattern::Empty);
        }
    }

    Ok(Alternation {
        patterns: alternates.into_iter().collect(),
    }
    .into_pattern())
}

// term = factor+
fn parse_term(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    let mut factors = Vec::new();

    while let Some(&c) = chars.peek() {
        if c == ')' || c == '|' {
            break; // End of term
        }
        let factor = parse_factor(chars)?;
        factors.push(factor);
    }

    if factors.is_empty() {
        return Err("Expected at least one factor".to_string());
    } else if factors.len() == 1 {
        return Ok(factors.remove(0));
    }

    Ok(Sequence { patterns: factors }.into_pattern())
}

// factor = base quantifier?
// quantifier = '*' | '+' | '?' | repetition
fn parse_factor(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    let base = parse_base(chars)?;

    Ok(match chars.next_if(|c| "*+?{".contains(*c)) {
        Some('*') => Pattern::repetition(Repetition {
            kind: RepetitionKind::ZeroOrMore,
            pattern: Box::new(base),
            greedy: true,
        }),
        Some('+') => Pattern::repetition(Repetition {
            kind: RepetitionKind::OneOrMore,
            pattern: Box::new(base),
            greedy: true,
        }),
        Some('?') => Pattern::repetition(Repetition {
            kind: RepetitionKind::Optional,
            pattern: Box::new(base),
            greedy: true,
        }),
        Some('{') => parse_repetition(chars, base)?,
        _ => base, // No quantifier, return base
    })
}

// repetition = '{n}' | '{n,m}' | '{n,}' | '{,m}'
fn parse_repetition(
    chars: &mut Peekable<impl Iterator<Item = char>>,
    base: Pattern,
) -> Result<Pattern, String> {
    let pattern = Box::new(base);

    fn expect_closing_brace(
        min: Option<usize>,
        max: Option<usize>,
        chars: &mut Peekable<impl Iterator<Item = char>>,
    ) -> Result<(Option<usize>, Option<usize>), String> {
        if let Some('}') = chars.next() {
            Ok((min, max))
        } else {
            Err("Expected closing '}'".to_string())
        }
    }

    let (min, max) = match chars.peek() {
        // {n} | {n,} | {n, m}
        Some(c) if c.is_digit(10) => {
            let min = parse_number(chars)?;
            match chars.peek() {
                // {n,} | {n, m}
                Some(',') => {
                    chars.next();
                    match chars.peek() {
                        // {n, m}
                        Some(c) if c.is_digit(10) => {
                            expect_closing_brace(Some(min), Some(parse_number(chars)?), chars)?
                        }
                        // {n,}
                        Some('}') => {
                            chars.next();
                            (Some(min), None)
                        }
                        _ => return Err("Expected number or closing '}'".to_string()),
                    }
                }
                // {n}
                Some(_) => expect_closing_brace(Some(min), Some(min), chars)?,
                None => return Err("Unexpected end of input".to_string()),
            }
        }
        // {,m}
        Some(',') => {
            chars.next();
            match chars.peek() {
                Some(c) if c.is_digit(10) => {
                    expect_closing_brace(None, Some(parse_number(chars)?), chars)?
                }
                _ => return Err("Expected number after ','".to_string()),
            }
        }
        _ => return Err("Expected a number or ',' after '{'".to_string()),
    };

    // Validate boundaries
    match (min, max) {
        (Some(min), Some(max)) if min > max => {
            return Err(format!(
                "Invalid repetition range: min {} > max {}",
                min, max
            ));
        }
        _ => Ok(Pattern::repetition(Repetition {
            pattern,
            kind: RepetitionKind::Range(min, max),
            greedy: true,
        })),
    }
}

fn parse_number(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<usize, String> {
    let mut num_str = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_digit(10) {
            num_str.push(c);
            chars.next();
        } else {
            break;
        }
    }
    num_str
        .parse::<usize>()
        .map_err(|_| "Invalid number".to_string())
}

// base = literal | '.' | '(' pattern ')' | character_class
fn parse_base(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    if chars.peek().is_some() {
        let (c, was_escaped) = parse_escaped_char(chars)?;
        return match (c, was_escaped) {
            ('.', false) => Ok(Pattern::Dot),
            ('(', false) => parse_group(chars),
            ('[', false) => parse_class(chars),
            ('*' | '+' | '?' | ')' | '|' | '{', false) => {
                Err(format!("Unexpected metacharacter '{}'", c))
            }
            _ => Ok(Pattern::Literal(c)),
        };
    }
    Err("Unexpected end of pattern".to_string())
}

fn parse_group(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    let inner_pattern = parse_pattern(chars)?;
    if chars.next() != Some(')') {
        return Err("Unmatched parentheses".to_string());
    }
    Ok(Pattern::Group(Box::new(inner_pattern)))
}

// character_class = '[' '^'? ']'? class_item+ ']'
// class_item = char | char '-' char
fn parse_class(chars: &mut Peekable<impl Iterator<Item = char>>) -> Result<Pattern, String> {
    let mut ranges = Vec::new();
    let negated = match chars.peek() {
        Some(&'^') => {
            chars.next();
            true
        }
        _ => false,
    };

    let mut prev: Option<char> = None;
    while chars.peek().is_some() {
        let (c, was_escaped) = parse_escaped_char(chars)?;
        match c {
            ']' => {
                if let Some(p) = prev {
                    ranges.push(p..=p);
                }
                if ranges.is_empty() {
                    // Treat ']' as a literal character
                    ranges.push(']'..=']');
                } else if was_escaped {
                    // If the last character was a backslash, treat ']' as a literal
                    ranges.push(']'..=']');
                } else {
                    return Ok(Pattern::character_class(CharacterClass { ranges, negated }));
                }
            }
            '-' => {
                if let Some(start) = prev.take() {
                    if let Some(&next_peek) = chars.peek() {
                        if next_peek == ']' {
                            // dash was literal
                            ranges.push(start..=start);
                            prev = Some('-');
                        } else if was_escaped {
                            // escaped (literal) dash
                            ranges.push(start..=start);
                            prev = Some('-');
                        } else {
                            let (end, _) = parse_escaped_char(chars)?;
                            if start > end {
                                return Err(format!("Invalid range {}-{}", start, next_peek));
                            }
                            ranges.push(start..=end);
                        }
                    } else {
                        return Err("Unexpected end after '-' in character class".to_string());
                    }
                } else {
                    prev = Some('-');
                }
            }
            _ => {
                if let Some(p) = prev.replace(c) {
                    ranges.push(p..=p);
                }
            }
        }
    }

    Err("Unclosed character class".to_string())
}

fn parse_escaped_char(
    chars: &mut Peekable<impl Iterator<Item = char>>,
) -> Result<(char, bool), String> {
    match chars.next() {
        Some('\\') => match chars.next() {
            Some(c @ ('\\' | '[' | ']' | '-' | '.' | '*' | '+' | '(' | ')' | '{' | '}')) => {
                Ok((c, true))
            }
            Some(c @ ('w' | 'W' | 'd' | 'D' | 's' | 'S')) => Ok((c, true)),
            Some(c) => Err(format!("Invalid escape sequence: \\{}", c)),
            None => Err("Unexpected end after backslash".to_string()),
        },
        Some(c) => Ok((c, false)),
        None => Err("Unexpected end of input".to_string()),
    }
}

//=== Tests ===

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_pattern() {
        let pattern = "(a|)";
        assert_eq!(match_pattern(pattern, "").unwrap(), true);
        assert_eq!(match_pattern(pattern, "a").unwrap(), true);
        assert_eq!(match_pattern("|a", "a").unwrap(), true);
        assert_eq!(match_pattern("|a", "").unwrap(), true);
        assert_eq!(match_pattern("a|", "a").unwrap(), true);
        assert_eq!(match_pattern("a|", "").unwrap(), true);
        assert_eq!(match_pattern("|", "").unwrap(), true);
        assert_eq!(match_pattern("|", "a").unwrap(), false);
    }

    #[test]
    fn test_class_literal_list() {
        let pattern = "[abc]";
        assert_eq!(match_pattern(pattern, "a").unwrap(), true);
        assert_eq!(match_pattern(pattern, "z").unwrap(), false);
        assert_eq!(match_pattern(pattern, "ab").unwrap(), false);
    }

    #[test]
    fn test_class_literal_range() {
        let pattern = "[a-z]";
        assert_eq!(match_pattern(pattern, "g").unwrap(), true);
        assert_eq!(match_pattern(pattern, "z").unwrap(), true);
        assert_eq!(match_pattern(pattern, "Z").unwrap(), false);
    }

    #[test]
    fn test_class_multiple_ranges() {
        let pattern = "[a-zA-Z]";
        assert_eq!(match_pattern(pattern, "D").unwrap(), true);
        assert_eq!(match_pattern(pattern, "b").unwrap(), true);
        assert_eq!(match_pattern(pattern, "0").unwrap(), false);
    }

    #[test]
    fn test_class_literal_hyphen_last() {
        let pattern = "[a-z-]";
        assert_eq!(match_pattern(pattern, "-").unwrap(), true);
        assert_eq!(match_pattern(pattern, "z").unwrap(), true);
    }

    #[test]
    fn test_class_literal_hyphen_first() {
        let pattern = "[-a-z]";
        assert_eq!(match_pattern(pattern, "-").unwrap(), true);
    }

    #[test]
    fn test_class_negated_range() {
        let pattern = "[^a-z]";
        assert_eq!(match_pattern(pattern, "A").unwrap(), true);
        assert_eq!(match_pattern(pattern, "a").unwrap(), false);
    }

    #[test]
    fn test_class_escaped_hyphen() {
        let pattern = r#"[a\-z]"#;
        assert_eq!(match_pattern(pattern, "-").unwrap(), true);
        assert_eq!(match_pattern(pattern, "a").unwrap(), true);
        assert_eq!(match_pattern(pattern, "c").unwrap(), false);
    }

    #[test]
    fn test_class_literal_slash() {
        let pattern = "[\\\\]";
        let input = "\\";
        assert_eq!(match_pattern(pattern, input).unwrap(), true);
    }

    #[test]
    fn test_class_literal_closing_bracket() {
        let pattern = "[]]";
        let input = "]";
        assert_eq!(match_pattern(pattern, input).unwrap(), true);
    }

    #[test]
    fn test_class_literal_opening_bracket() {
        let pattern = "[[]";
        let input = "[";
        assert_eq!(match_pattern(pattern, input).unwrap(), true);
    }

    #[test]
    fn test_class_literal_closing_bracket_outside() {
        let pattern = "[a]b]";
        let input = "ab]";
        assert_eq!(match_pattern(pattern, input).unwrap(), true);
    }

    #[test]
    fn test_repetition_exact_ascii() {
        let pattern = "a{3}";
        let input = "aaa";
        assert_eq!(match_pattern(pattern, input).unwrap(), true);
    }

    #[test]
    fn test_repetition_range_ascii() {
        let pattern = "a{2,4}";
        assert_eq!(match_pattern(pattern, "aa").unwrap(), true);
        assert_eq!(match_pattern(pattern, "aaa").unwrap(), true);
        assert_eq!(match_pattern(pattern, "aaaa").unwrap(), true);
        assert_eq!(match_pattern(pattern, "a").unwrap(), false);
        assert_eq!(match_pattern(pattern, "aaaaa").unwrap(), false);
    }

    #[test]
    fn test_repetition_open_upper() {
        let pattern = "b{2,}";
        assert_eq!(match_pattern(pattern, "bb").unwrap(), true);
        assert_eq!(match_pattern(pattern, "bbbbbbb").unwrap(), true);
        assert_eq!(match_pattern(pattern, "b").unwrap(), false);
    }

    #[test]
    fn test_repetition_open_lower() {
        let pattern = "c{,3}";
        assert_eq!(match_pattern(pattern, "").unwrap(), true);
        assert_eq!(match_pattern(pattern, "c").unwrap(), true);
        assert_eq!(match_pattern(pattern, "cc").unwrap(), true);
        assert_eq!(match_pattern(pattern, "ccc").unwrap(), true);
        assert_eq!(match_pattern(pattern, "cccc").unwrap(), false);
    }

    #[test]
    fn test_repetition_exact_unicode() {
        let pattern = "[😀-🙏]{3}";
        assert_eq!(match_pattern(pattern, "😁😁😁").unwrap(), true);
        assert_eq!(match_pattern(pattern, "🙏").unwrap(), false);
    }

    #[test]
    fn test_repetition_unicode_range_and_length() {
        // Range: 🐱 (U+1F431) to 🦁 (U+1F981)
        let pattern = "[🐱-🦁]{2,4}";
        assert_eq!(match_pattern(pattern, "🐱🐶").unwrap(), true);
        assert_eq!(match_pattern(pattern, "🐱🐶🦁").unwrap(), true);
        assert_eq!(match_pattern(pattern, "🐱").unwrap(), false);
        assert_eq!(match_pattern(pattern, "🐱🐶🦁🦁🦁").unwrap(), false);
    }

    #[test]
    fn pattern_size() {
        let max = 2 * core::mem::size_of::<usize>();
        let size = core::mem::size_of::<Pattern>();
        assert!(
            size <= max,
            "Pattern size of {} is bigger than suggested max {}",
            size,
            max
        );
    }
}
