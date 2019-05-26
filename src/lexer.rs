#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Loc(usize, usize);

impl Loc {
    fn merge(&self, other: &Loc) -> Loc {
        use std::cmp::{max, min};
        Loc(min(self.0, other.0), max(self.1, other.1))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Annot<T> {
    value: T,
    loc: Loc,
}

impl<T> Annot<T> {
    fn new(value: T, loc: Loc) -> Self {
        Self { value, loc }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Number(u64),
    Plus,
    Minus,
    Asterisk,
    Slash,
    LParen,
    RParen,
}

type Token = Annot<TokenKind>;

impl Token {
    fn number(n: u64, loc: Loc) -> Self {
        Self::new(TokenKind::Number(n), loc)
    }

    fn plus(loc: Loc) -> Self {
        Self::new(TokenKind::Plus, loc)
    }

    fn minus(loc: Loc) -> Self {
        Self::new(TokenKind::Minus, loc)
    }

    fn asterisk(loc: Loc) -> Self {
        Self::new(TokenKind::Asterisk, loc)
    }

    fn slash(loc: Loc) -> Self {
        Self::new(TokenKind::Slash, loc)
    }

    fn lparen(loc: Loc) -> Self {
        Self::new(TokenKind::LParen, loc)
    }

    fn rparen(loc: Loc) -> Self {
        Self::new(TokenKind::RParen, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LexErrorKind {
    InvalidChar(char),
    Eof,
}

pub type LexError = Annot<LexErrorKind>;

impl LexError {
    fn invalid_char(c: char, loc: Loc) -> Self {
        LexError::new(LexErrorKind::InvalidChar(c), loc)
    }

    fn eof(loc: Loc) -> Self {
        LexError::new(LexErrorKind::Eof, loc)
    }
}

// Lexer
pub fn lex(input: &str) -> Result<Vec<Token>, LexError> {
    let mut tokens = Vec::new();
    let input = input.as_bytes();
    let mut pos = 0;
    macro_rules! lex_a_token {
        ($lexer:expr) => {{
            let (tok, p) = $lexer?;
            tokens.push(tok);
            pos = p;
        }};
    }
    while pos < input.len() {
        match input[pos] {
            b'0'...b'9' => lex_a_token!(lex_number(input, pos)),
            b'+' => lex_a_token!(lex_plus(input, pos)),
            b'-' => lex_a_token!(lex_minus(input, pos)),
            b'*' => lex_a_token!(lex_asterisc(input, pos)),
            b'/' => lex_a_token!(lex_slash(input, pos)),
            b'(' => lex_a_token!(lex_lparen(input, pos)),
            b')' => lex_a_token!(lex_rparen(input, pos)),
            b' ' | b'\n' | b'\t' => {
                let ((), p) = skip_spaces(input, pos)?;
                pos = p;
            }
            b => return Err(LexError::invalid_char(b as char, Loc(pos, pos + 1))),
        }
    }
    Ok(tokens)
}

fn consume_byte(input: &[u8], pos: usize, b: u8) -> Result<(u8, usize), LexError> {
    if input.len() <= pos {
        return Err(LexError::eof(Loc(pos, pos)));
    }

    if input[pos] != b {
        return Err(LexError::invalid_char(
            input[pos] as char,
            Loc(pos, pos + 1),
        ));
    }

    Ok((b, pos + 1))
}

fn lex_number(input: &[u8], pos: usize) -> Result<(Token, usize), LexError> {
    use core::str::from_utf8;
    let start = pos;
    let end = recognize_many(input, pos, |b| b"0123456789".contains(&b));
    let n = from_utf8(&input[start..end]).unwrap().parse().unwrap();
    Ok((Token::number(n, Loc(start, end)), end))
}

fn skip_spaces(input: &[u8], pos: usize) -> Result<((), usize), LexError> {
    let pos = recognize_many(input, pos, |b| b" \n\t".contains(&b));
    Ok(((), pos))
}

fn recognize_many(input: &[u8], mut pos: usize, mut f: impl FnMut(u8) -> bool) -> usize {
    while pos < input.len() && f(input[pos]) {
        pos += 1;
    }
    pos
}

fn lex_plus(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'+').map(|(_, end)| (Token::plus(Loc(start, end)), end))
}

fn lex_minus(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'-').map(|(_, end)| (Token::minus(Loc(start, end)), end))
}

fn lex_asterisc(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'*').map(|(_, end)| (Token::asterisk(Loc(start, end)), end))
}

fn lex_slash(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'/').map(|(_, end)| (Token::slash(Loc(start, end)), end))
}

fn lex_lparen(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'(').map(|(_, end)| (Token::lparen(Loc(start, end)), end))
}

fn lex_rparen(input: &[u8], start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b')').map(|(_, end)| (Token::rparen(Loc(start, end)), end))
}

#[test]
fn test_lexer() {
    assert_eq!(
        lex("(1 + 2) * 3 - -8 / 1"),
        Ok(vec![
            Token::lparen(Loc(0, 1)),
            Token::number(1, Loc(1, 2)),
            Token::plus(Loc(3, 4)),
            Token::number(2, Loc(5, 6)),
            Token::rparen(Loc(6, 7)),
            Token::asterisk(Loc(8, 9)),
            Token::number(3, Loc(10, 11)),
            Token::minus(Loc(12, 13)),
            Token::minus(Loc(14, 15)),
            Token::number(8, Loc(15, 16)),
            Token::slash(Loc(17, 18)),
            Token::number(1, Loc(19, 20)),
        ])
    )
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum AstKind {
    Num(u64),
    UniOp { op: UniOp, e: Box<Ast> },
    BinOp { op: BinOp, l: Box<Ast>, r: Box<Ast> },
}

type Ast = Annot<AstKind>;

impl Ast {
    fn num(n: u64, loc: Loc) -> Self {
        Self::new(AstKind::Num(n), loc)
    }

    fn uniop(op: UniOp, e: Ast, loc: Loc) -> Self {
        Self::new(AstKind::UniOp { op, e: Box::new(e) }, loc)
    }

    fn binop(op: BinOp, l: Ast, r: Ast, loc: Loc) -> Self {
        Self::new(
            AstKind::BinOp {
                op,
                l: Box::new(l),
                r: Box::new(r),
            },
            loc,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum UniOpKind {
    Plus,
    Minus,
}

type UniOp = Annot<UniOpKind>;

impl UniOp {
    fn plus(loc: Loc) -> Self {
        Self::new(UniOpKind::Plus, loc)
    }

    fn minus(loc: Loc) -> Self {
        Self::new(UniOpKind::Minus, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum BinOpKind {
    Add,
    Sub,
    Mult,
    Div,
}

type BinOp = Annot<BinOpKind>;

impl BinOp {
    fn add(loc: Loc) -> Self {
        Self::new(BinOpKind::Add, loc)
    }

    fn sub(loc: Loc) -> Self {
        Self::new(BinOpKind::Sub, loc)
    }

    fn mult(loc: Loc) -> Self {
        Self::new(BinOpKind::Mult, loc)
    }

    fn div(loc: Loc) -> Self {
        Self::new(BinOpKind::Div, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ParseError {
    UnexpectedToken(Token),
    NotExpression(Token),
    NotOperator(Token),
    UnclosedOpenParser(Token),
    RedundantExpression(Token),
    Eof,
}

pub fn parse(tokens: Vec<Token>) -> Result<Ast, ParseError> {
    let mut tokens = tokens.into_iter().peekable();
    let ret = parse_expr(&mut tokens)?;
    match tokens.next() {
        Some(tok) => Err(ParseError::RedundantExpression(tok)),
        None => Ok(ret),
    }
}

use std::iter::Peekable;

// EXPR = EXPR3;
fn parse_expr<Tokens>(tokens: &mut Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    parse_expr3(tokens)
}

// EXPR3 = EXPR2 EXPR3_Loop
// EXPR3_Loop = ("+" | "-") EXPR2 EXPR3_Loop | ε
fn parse_expr3<Tokens>(tokens: &mut Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    let mut e = parse_expr2(tokens)?;
    // EXPR3_Loop
    loop {
        match tokens.peek().map(|tok| tok.value) {
            Some(TokenKind::Plus) | Some(TokenKind::Minus) => {
                let op = match tokens.next().unwrap() {
                    Token {
                        value: TokenKind::Plus,
                        loc,
                    } => BinOp::add(loc),
                    Token {
                        value: TokenKind::Minus,
                        loc,
                    } => BinOp::sub(loc),
                    _ => unreachable!(),
                };
                let r = parse_expr2(tokens)?;
                let loc = e.loc.merge(&r.loc);
                e = Ast::binop(op, e, r, loc)
            }
            _ => return Ok(e),
        }
    }
}

// EXPR2 = EXPR1 EXPR2_Loop
// EXPR2_Loop = ("*" | "/") EXPR1 EXPR2_Loop | ε
fn parse_expr2<Tokens>(tokens: &mut Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    let mut e = parse_expr1(tokens)?;
    // EXPR2_Loop
    loop {
        match tokens.peek().map(|tok| tok.value) {
            Some(TokenKind::Asterisk) | Some(TokenKind::Slash) => {
                let op = match tokens.next().unwrap() {
                    Token {
                        value: TokenKind::Asterisk,
                        loc,
                    } => BinOp::add(loc),
                    Token {
                        value: TokenKind::Slash,
                        loc,
                    } => BinOp::sub(loc),
                    _ => unreachable!(),
                };
                let r = parse_expr1(tokens)?;
                let loc = e.loc.merge(&r.loc);
                e = Ast::binop(op, e, r, loc)
            }
            _ => return Ok(e),
        }
    }
}

// EXPR1 = ("+" | "-") ATOM
fn parse_expr1<Tokens>(tokens: &mut Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    match tokens.peek().map(|tok| tok.value) {
        Some(TokenKind::Plus) | Some(TokenKind::Minus) => {
            let op = match tokens.next() {
                Some(Token {
                    value: TokenKind::Plus,
                    loc,
                }) => UniOp::plus(loc),
                Some(Token {
                    value: TokenKind::Minus,
                    loc,
                }) => UniOp::minus(loc),
                _ => unreachable!(),
            };
            let e = parse_atom(tokens)?;
            let loc = op.loc.merge(&e.loc);
            Ok(Ast::uniop(op, e, loc))
        }
        _ => parse_atom(tokens),
    }
}

// ATOM = UNUMBER | "(" EXPR3 ")"
fn parse_atom<Tokens>(tokens: &mut Peekable<Tokens>) -> Result<Ast, ParseError>
where
    Tokens: Iterator<Item = Token>,
{
    tokens
        .next()
        .ok_or(ParseError::Eof)
        .and_then(|tok| match tok.value {
            TokenKind::Number(n) => Ok(Ast::new(AstKind::Num(n), tok.loc)),
            TokenKind::LParen => {
                let e = parse_expr(tokens)?;
                match tokens.next() {
                    Some(Token {
                        value: TokenKind::RParen,
                        ..
                    }) => Ok(e),
                    Some(t) => Err(ParseError::RedundantExpression(t)),
                    _ => Err(ParseError::UnclosedOpenParser(tok)),
                }
            }
            _ => Err(ParseError::NotExpression(tok)),
        })
}

#[test]
fn test_parser() {
    // 1 + 2 * 3 - -10
    let ast = parse(vec![
        Token::number(1, Loc(0, 1)),
        Token::plus(Loc(2, 3)),
        Token::number(2, Loc(4, 5)),
        Token::asterisk(Loc(6, 7)),
        Token::number(3, Loc(8, 9)),
        Token::minus(Loc(10, 11)),
        Token::minus(Loc(12, 13)),
        Token::number(10, Loc(13, 15)),
    ]);
    assert_eq!(
        ast,
        Ok(Ast::binop(
            BinOp::sub(Loc(10, 11)),
            Ast::binop(
                BinOp::add(Loc(2, 3)),
                Ast::num(1, Loc(0, 1)),
                Ast::binop(
                    BinOp::new(BinOpKind::Mult, Loc(6, 7)),
                    Ast::num(2, Loc(4, 5)),
                    Ast::num(3, Loc(8, 9)),
                    Loc(4, 9)
                ),
                Loc(0, 9),
            ),
            Ast::uniop(
                UniOp::minus(Loc(12, 13)),
                Ast::num(10, Loc(13, 15)),
                Loc(12, 15)
            ),
            Loc(0, 15)
        ))
    )
}
