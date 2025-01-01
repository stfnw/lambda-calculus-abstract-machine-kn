/// This module implements encoding/decoding routines for lambda terms in
/// John Tromp's Binary Lambda Calculus notation. See
/// https://tromp.github.io/cl/Binary_lambda_calculus.html#lambda_encoding.
/// Note that this is very limited and not a full evaluator of BLC like the implementation
/// from John Tromp available e.g. at https://github.com/tromp/AIT/blob/master/uni.c:
/// E.g. it does not implement the input decoding / output encoding of lambda terms as
/// list of bits / bit-strings.
use crate::Term;

use std::rc::Rc;

/// Convert BLC string into lambda term/expression AST.
pub fn decode(blc: &str) -> Term {
    let tokens = lex(blc);
    parse(&tokens)
}

/// Encode a lambda expression/term into BLC format.
/// This pre-order AST traversal is implemented iteratively in order to not run
/// into stack limits for large terms.
pub fn encode(term: &Term) -> String {
    let mut res = Vec::new();

    let action = |term: &Term| match term {
        Term::Var { debruijn } => res.push(format!("{}0", "1".repeat(*debruijn + 1))),
        Term::Abs { body: _ } => res.push("00".to_string()),
        Term::App { func: _, arg: _ } => res.push("01".to_string()),
    };

    term.preorder_traverse(action);

    res.join("")
}

#[derive(Debug, PartialEq)]
pub enum Token {
    Var { debruijn: usize }, // variable
    Abs,                     // abstraction
    App,                     // application
}

/// Tokenize a string in binary lambda calculus encoding.
fn lex(blc: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = blc.chars();

    while let Some(c) = chars.next() {
        match c {
            '0' => match chars.next().unwrap() {
                '0' => tokens.push(Token::Abs),
                '1' => tokens.push(Token::App),
                cc => panic!("Unexpected character {} (expected 0 or 1)", cc),
            },
            '1' => {
                let mut debruijn = 0;
                loop {
                    match chars.next().unwrap() {
                        '0' => break,
                        '1' => debruijn += 1,
                        cc => panic!("Unexpected character {} (exptected 0 or 1)", cc),
                    }
                }
                tokens.push(Token::Var { debruijn });
            }
            cc => panic!("Unexpected character {} (exptected 0 or 1)", cc),
        }
    }

    tokens
}

/// Parse a list of tokens into a lambda expression. This is done iteratively
/// in order to not run into stack limits for large terms. Also makes sure that
/// the term is closed / all variables are bound.
fn parse(tokens: &[Token]) -> Term {
    let mut stack: Vec<Term> = Vec::new();

    for token in tokens.iter().rev() {
        match token {
            Token::Var { debruijn } => stack.push(Term::Var {
                debruijn: *debruijn,
            }),
            Token::Abs => {
                let body = Rc::new(stack.pop().unwrap());
                stack.push(Term::Abs { body });
            }
            Token::App => {
                let func = Rc::new(stack.pop().unwrap());
                let arg = Rc::new(stack.pop().unwrap());
                stack.push(Term::App { func, arg });
            }
        }
    }

    if stack.len() != 1 {
        panic!(
            "Stack contains not exactly one element after parsing! {:?}",
            stack
        );
    }

    let term = stack.pop().unwrap();

    verify_closed(&term);

    term
}

/// Make sure that the provided term is closed.
fn verify_closed(term: &Term) {
    let mut stack: Vec<(usize, &Term)> = Vec::new();
    stack.push((0, term));

    while let Some((depth, node)) = stack.pop() {
        match node {
            Term::Var { debruijn } => {
                if depth <= *debruijn {
                    panic!("Provided term {} is not closed", term);
                }
            }
            Term::Abs { body } => stack.push((depth + 1, body)),
            Term::App { func, arg } => {
                stack.push((depth, arg));
                stack.push((depth, func));
            }
        }
    }
}
