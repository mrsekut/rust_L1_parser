use crate::lexer::{lex, Annot, Loc, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AstKind {
    Num(u64),
    UniOp { op: UniOp, e: Box<Ast> },
    BinOp { op: BinOp, l: Box<Ast>, r: Box<Ast> },
}

pub type Ast = Annot<AstKind>;

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

use crate::error;
use std::str::FromStr;
impl FromStr for Ast {
    type Err = error::Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = lex(s)?;
        let ast = parse(tokens)?;
        Ok(ast)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum UniOpKind {
    Plus,
    Minus,
}

pub type UniOp = Annot<UniOpKind>;

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

pub type BinOp = Annot<BinOpKind>;

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
pub enum ParseError {
    UnexpectedToken(Token),
    NotExpression(Token),
    NotOperator(Token),
    UnclosedOpenParen(Token),
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

// TODO: 共通化

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
                    _ => Err(ParseError::UnclosedOpenParen(tok)),
                }
            }
            _ => Err(ParseError::NotExpression(tok)),
        })
}

// #[test]
// fn test_parser() {
//     // 1 + 2 * 3 - -10
//     let ast = parse(vec![
//         Token::number(1, Loc(0, 1)),
//         Token::plus(Loc(2, 3)),
//         Token::number(2, Loc(4, 5)),
//         Token::asterisk(Loc(6, 7)),
//         Token::number(3, Loc(8, 9)),
//         Token::minus(Loc(10, 11)),
//         Token::minus(Loc(12, 13)),
//         Token::number(10, Loc(13, 15)),
//     ]);
//     assert_eq!(
//         ast,
//         Ok(Ast::binop(
//             BinOp::sub(Loc(10, 11)),
//             Ast::binop(
//                 BinOp::add(Loc(2, 3)),
//                 Ast::num(1, Loc(0, 1)),
//                 Ast::binop(
//                     BinOp::new(BinOpKind::Mult, Loc(6, 7)),
//                     Ast::num(2, Loc(4, 5)),
//                     Ast::num(3, Loc(8, 9)),
//                     Loc(4, 9)
//                 ),
//                 Loc(0, 9),
//             ),
//             Ast::uniop(
//                 UniOp::minus(Loc(12, 13)),
//                 Ast::num(10, Loc(13, 15)),
//                 Loc(12, 15)
//             ),
//             Loc(0, 15)
//         ))
//     )
// }
