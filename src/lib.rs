//! This module implements normal-order evaluation of pure/untyped lambda
//! calculus terms. It does this through a full-reducing variant (KN) of the
//! Krivine abstract machine introduced in [1].
//!
//! More specifically, the KN formulation/variant as outlined in [2],
//! Fig. 3. "A version of KN that works with closures with closed terms"
//! is used.
//! Section 4 "The KN machine and its improved open-terms version" of [2]
//! describes the workings in detail.
//!
//! [1] P. Crégut, "Strongly reducing variants of the Krivine abstract machine", Higher-Order Symb Comput, vol. 20, no. 3, pp. 209–230, Nov. 2007, doi: 10.1007/s10990-007-9015-z.
//! [2] Á. García-Pérez and P. Nogueira, "The full-reducing Krivine abstract machine KN simulates pure normal-order reduction in lockstep: A proof via corresponding calculus", J. Funct. Prog., vol. 29, p. e7, 2019, doi: 10.1017/S0956796819000017.

use std::fmt;
use std::rc::Rc;

pub mod format;

use format::named;

/// Lambda expression / term. These use a nameless representation of Lambda
/// terms with De Bruijn indices.
#[derive(Clone)]
pub enum Term {
    Var { debruijn: usize },
    Abs { body: Rc<Term> },
    App { func: Rc<Term>, arg: Rc<Term> },
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", named::encode(self))
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", named::encode_to_debruijn(self))
    }
}

impl Term {
    /// Traverse the ast of a lambda expression in pre-order and perform some
    /// action on each node.
    pub fn preorder_traverse<F>(&self, mut action: F)
    where
        F: FnMut(&Term),
    {
        let mut stack = Vec::new();
        stack.push(self);

        while let Some(node) = stack.pop() {
            action(node);
            match node {
                Term::Var { debruijn: _ } => (),
                Term::Abs { body } => stack.push(body),
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
enum Closure {
    Proper { term: Rc<Term>, env: Rc<Env> },
    Level(usize),
    Res { term: Rc<Term>, level: usize },
}

type Env = Vec<Closure>;

#[derive(Debug)]
enum Frame {
    Closure { term: Rc<Term>, env: Rc<Env> },
    Lambda,
    Res { term: Rc<Term>, level: usize },
}

pub fn eval(term: Term) -> Term {
    krivine(term)
}

fn krivine(term: Term) -> Term {
    // [2, Fig. 3]: Rule (1)
    let mut closure: Closure = Closure::Proper {
        term: term.into(),
        env: Rc::new(Vec::new()),
    };
    let mut stack: Vec<Frame> = Vec::new();
    let mut level = 0;

    loop {
        // println!("Machine State:");
        // println!("  - closure: {:?}", closure);
        // println!("  - stack:   {:?}", stack);
        // println!("  - level:   {:?}", level);
        match closure {
            Closure::Proper { term, env } => {
                match term.as_ref() {
                    Term::Var { debruijn } => {
                        // println!("[2, Fig. 3]: Rule (2) and (3)");
                        // Because we push new closures / extend the environment
                        // to the right, we also have to pop / access indices
                        // into the environment from the right side!
                        let i = env.len() - 1 - debruijn;
                        closure = env[i].clone();
                    }
                    Term::App { func, arg } => {
                        // println!("[2, Fig. 3]: Rule (4)");
                        closure = Closure::Proper {
                            term: Rc::clone(func),
                            env: env.clone(),
                        };
                        stack.push(Frame::Closure {
                            term: Rc::clone(arg),
                            env,
                        });
                    }
                    Term::Abs { body } => match stack.last() {
                        Some(Frame::Closure { term: ft, env: fe }) => {
                            // println!("[2, Fig. 3]: Rule (5)");
                            let mut newenv = (*env).clone();
                            newenv.push(Closure::Proper {
                                term: Rc::clone(ft),
                                env: Rc::clone(fe),
                            });
                            closure = Closure::Proper {
                                term: Rc::clone(body),
                                env: Rc::new(newenv),
                            };
                            stack.pop();
                        }
                        _ => {
                            // println!("[2, Fig. 3]: Rule (6)");
                            let mut newenv = (*env).clone();
                            newenv.push(Closure::Level(level + 1));
                            closure = Closure::Proper {
                                term: Rc::clone(body),
                                env: Rc::new(newenv),
                            };
                            stack.push(Frame::Lambda);
                            level += 1;
                        }
                    },
                }
            }

            Closure::Level(n) => {
                // println!("[2, Fig. 3]: Rule (7)");
                closure = Closure::Res {
                    term: Rc::new(Term::Var {
                        debruijn: level - n,
                    }),
                    level,
                }
            }

            Closure::Res { term: t, level: l } => match stack.pop() {
                Some(Frame::Closure { term: ft, env: fe }) => {
                    // println!("[2, Fig. 3]: Rule (8)");
                    closure = Closure::Proper { term: ft, env: fe };
                    stack.push(Frame::Res { term: t, level: l });
                    level = l;
                }
                Some(Frame::Lambda) => {
                    // println!("[2, Fig. 3]: Rule (9)");
                    closure = Closure::Res {
                        term: Rc::new(Term::Abs { body: t }),
                        level: l,
                    };
                }
                Some(Frame::Res {
                    term: ft,
                    level: fl,
                }) => {
                    // println!("[2, Fig. 3]: Rule (10)");
                    closure = Closure::Res {
                        term: Rc::new(Term::App { func: ft, arg: t }),
                        level: fl,
                    };
                }
                None => return (*t).clone(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use format::{blc, named};

    struct ConvertTestCase {
        blc: &'static str,
        debruijn: &'static str,
        named: &'static str,
    }

    /// Test conversions (lexing and parsing and displaying) from/to various
    /// formats. Test cases are built from the examples in
    /// https://tromp.github.io/cl/Binary_lambda_calculus.html
    /// and https://justine.lol/lambda/.
    #[test]
    fn test_convert() {
        let cases = [
            ConvertTestCase {
                blc: "0010",
                debruijn: "(λ 0)",
                named: "(λa. a)",
            },
            ConvertTestCase {
                blc: "010001101000011010",
                debruijn: "((λ (0 0)) (λ (0 0)))",
                named: "((λa. (a a)) (λa. (a a)))",
            },
            ConvertTestCase {
                // addition
                blc: "000000000101111101100101111011010",
                debruijn: "(λ (λ (λ (λ ((3 1) ((2 1) 0))))))",
                named: "(λa. (λb. (λc. (λd. ((a c) ((b c) d))))))",
            },
            ConvertTestCase {
                // even predicate
                blc: "00010001101000000101100000100001011000001100111101110",
                debruijn: "(λ ((λ (0 0)) (λ (λ ((0 (λ (λ 0))) (λ ((0 (λ (λ 1))) (2 2))))))))",
                named: "(λa. ((λb. (b b)) (λb. (λc. ((c (λd. (λe. e))) (λd. ((d (λe. (λf. e))) (b b))))))))",
            },
            // universal machine
            ConvertTestCase {
                blc: "0101000110100000000101011000000000011110000101111110011110000101110011110000001111000010110110111001111100001111100001011110100111010010110011100001101100001011111000011111000011100110111101111100111101110110000110010001101000011010",
                debruijn: "(((λ (0 0)) (λ (λ (λ (((0 (λ (λ (λ (λ (2 (λ ((4 (2 (λ ((1 (2 (λ (λ (2 (λ ((0 1) 2))))))) (3 (λ (3 (λ ((2 0) (1 0)))))))))) ((0 (1 (λ (0 1)))) (λ ((3 (λ (3 (λ (1 (0 3)))))) 4))))))))))) (2 2)) 1))))) (λ (0 ((λ (0 0)) (λ (0 0))))))",
                named: "(((λa. (a a)) (λa. (λb. (λc. (((c (λd. (λe. (λf. (λg. (e (λh. ((d (f (λi. ((h (g (λj. (λk. (i (λl. ((l k) j))))))) (f (λj. (g (λk. ((i k) (j k)))))))))) ((h (g (λi. (i h)))) (λi. ((f (λj. (g (λk. (j (k h)))))) e))))))))))) (a a)) b))))) (λa. (a ((λb. (b b)) (λb. (b b))))))",
            },
        ];

        for case in cases {
            let ast = blc::decode(case.blc);
            println!("AST from binary {:?}", ast);
            assert_eq!(case.blc, blc::encode(&ast));
            assert_eq!(case.debruijn, named::encode_to_debruijn(&ast));
            assert_eq!(case.named, named::encode(&ast));

            let ast = named::decode(case.named);
            println!("AST from text {:?}", ast);
            assert_eq!(case.blc, blc::encode(&ast));
            assert_eq!(case.debruijn, named::encode_to_debruijn(&ast));
            assert_eq!(case.named, named::encode(&ast));
        }
    }

    struct EvalTestCase<'a> {
        comment: &'a str,
        term: &'a str,
        reduced: &'a str,
    }

    /// Test correct beta reduction of various terms.
    #[test]
    fn test_eval() {
        let cases = [
            EvalTestCase {
                comment: "I",
                term: "(λa. a)",
                reduced: "(λa. a)",
            },
            EvalTestCase {
                comment: "(ω I)",
                term: "((λa. (a a)) (λa. a))",
                reduced: "(λa. a)",
            },
            EvalTestCase {
                comment: "((I I) I)",
                term: "(((λa. a) (λa. a)) (λa. a))",
                reduced: "(λa. a)",
            },
            EvalTestCase {
                comment: "(false I)",
                term: "((λa. (λb. b)) (λa. a))",
                reduced: "(λa. a)",
            },
            EvalTestCase {
                comment: "(true I)",
                term: "((λa. (λb. a)) (λa. a))",
                reduced: "(λa. (λb. b))",
            },
            EvalTestCase {
                comment: "((true I) I)",
                term: "(((λa. (λb. a)) (λa. a)) (λa. a))",
                reduced: "(λa. a)",
            },

            EvalTestCase {
                comment: "-",
                term: "((λa. (λb. (a b))) (λa. a))",
                reduced: "(λa. a)",
            },
            EvalTestCase {
                comment: "-",
                term: "((λa. (λb. (b a))) (λa. (λb. (a b))))",
                reduced: "(λa. (a (λb. (λc. (b c)))))",
            },

            /* Some more elaborate tests: generated in bash with the following
             * shortcuts, also see https://en.wikipedia.org/wiki/Church_encoding.

            # boolean logic
            TRUE="(λx. (λy. x))"
            FALSE="(λx. (λy. y))"
            AND="(λp. (λq. ((p q) p)))"
            OR="(λp. (λq. ((p p) q)))"
            IF="(λp. (λa. (λb. ((p a) b))))"

            # lists / bitstrings
            BIT0="$TRUE"
            BIT1="$FALSE"
            NIL="$FALSE"
            CONS="(λx. (λy. (λz. ((z x) y))))"
            CAR="(λp. (p (λx. (λy. x))))"
            CDR="(λp. (p (λx. (λy. y))))"

            # arithmetic / church numerals
            ZERO="(λf. (λx. x))"
            ONE="(λf. (λx. (f x)))"
            TWO="(λf. (λx. (f (f x))))"
            THREE="(λf. (λx. (f (f (f x)))))"
            FOUR="(λf. (λx. (f (f (f (f x))))))"
            ADD="(λm. (λn. (λf. (λx. ((m f) ((n f) x))))))"
            MUL="(λm. (λn. (λf. (λx. (m (n f))))))"

             */

            EvalTestCase {
                comment: "(($AND $TRUE) $FALSE)",
                term: "(((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f)))",
                reduced: "(λa. (λb. b))", // $FALSE
            },
            EvalTestCase {
                comment: "($NOT (($AND $TRUE) $FALSE))",
                term: "((λp. (λa. (λb. ((p b) a)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f))))",
                reduced: "(λa. (λb. a))", // $TRUE
            },
            EvalTestCase {
                comment: "($IF (($AND $TRUE) (($OR $TRUE) $FALSE)))",
                term: "((λp. (λa. (λb. ((p a) b)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (((λp. (λq. ((p p) q))) (λt. (λf. t))) (λt. (λf. f)))))",
                reduced: "(λa. (λb. a))", // $TRUE
            },
            EvalTestCase {
                comment: "($IF (($AND $TRUE) (($AND $TRUE) $FALSE)))",
                term: "((λp. (λa. (λb. ((p a) b)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f)))))",
                reduced: "(λa. (λb. b))", // $FALSE
            },

            EvalTestCase {
                comment: "(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL)))) -- binary string: [1101]",
                term: "(((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))",
                reduced: "(λa. ((a (λb. (λc. c))) (λb. ((b (λc. (λd. d))) (λc. ((c (λd. (λe. d))) (λd. ((d (λe. (λf. f))) (λe. (λf. f))))))))))",
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR $LIST)\"",
                term: "((λp. (p (λx. (λy. x)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))",
                reduced: "(λa. (λb. b))", // 1
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CDR $LIST)\"",
                term: "((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))",
                reduced: "(λa. ((a (λb. (λc. c))) (λb. ((b (λc. (λd. c))) (λc. ((c (λd. (λe. e))) (λd. (λe. e))))))))", // [101]
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR $LIST))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))))",
                reduced: "(λa. (λb. b))", // 1
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR ($CDR $LIST)))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))))",
                reduced: "(λa. (λb. a))", // 0
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CDR ($CDR ($CDR $LIST)))\"",
                term: "((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))))",
                reduced: "(λa. ((a (λb. (λc. c))) (λb. (λc. c))))", // [1]
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR ($CDR ($CDR $LIST))))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))))))",
                reduced: "(λa. (λb. b))", // 1
            },

            EvalTestCase {
                comment: "(($ADD $TWO) $FOUR)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a b))))))))", // 6
            },
            EvalTestCase {
                comment: "(($ADD (($ADD (($ADD $TWO) $FOUR)) $ONE)) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (λf. (λx. (f x))))) (λf. (λx. (f (f (f x))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($ADD (($ADD $TWO) $FOUR)) (($ADD $ONE) $THREE))",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f x)))) (λf. (λx. (f (f (f x)))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($MUL $TWO) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f x))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a b))))))))", // 6
            },
            EvalTestCase {
                comment: "(($MUL $FOUR) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f (f (f x))))))) (λf. (λx. (f (f (f x))))))", 
                reduced: "(λa. (λb. (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))", // 12
            },
            EvalTestCase {
                comment: "(($ADD (($MUL $TWO) $THREE)) $FOUR)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f x))))))) (λf. (λx. (f (f (f (f x)))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($ADD $FOUR) (($MUL $THREE) $TWO))",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f (f (f x))))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f (f x)))))) (λf. (λx. (f (f x))))))",
                reduced: "(λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))", // 10
            },
        ];

        for case in cases {
            println!("comment {}", case.comment);
            let ast = named::decode(case.term);
            println!("parsed  {}", ast);
            println!("        {:?}", ast);
            let reduced = eval(ast);
            println!("reduced {}", reduced);
            println!("        {:?}", reduced);
            assert_eq!(case.reduced, named::encode(&reduced));
            println!();
        }
    }

    #[test]
    fn test_main() {
        let code = "01010000000001011111011001011110110100101000000000101111101100101111011010000001110011101000000111001110011100111010010100000000010111110110010111101101000000111010000001110011100111010";
        let term = blc::decode(code);
        println!("term:           {}", term);
        let reduced = eval(term);
        println!("term (reduced): {}", reduced);
        assert_eq!(
            blc::encode(&reduced),
            "00000111001110011100111001110011100111001110011100111010"
        );
    }
}
