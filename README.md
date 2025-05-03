This is a demo project implementing normal-order evaluation of untyped lambda calculus terms.
(Goal is me learning; this project will probably not be maintained further).
It does this through a full-reducing variant (KN) of the Krivine abstract machine introduced in [^1].

More specifically, the KN formulation/variant as outlined in [^2], Fig. 3. "A version of KN that works with closures with closed terms" is used.
Section 4 "The KN machine and its improved open-terms version" of [^2] describes the workings in detail.

In KN, variables are represented as De Bruijn indices and evaluation is implemented using closures (terms together with the environments in which they are evaluated).
This allows for an easy implementation of normal-order beta-reduction (which is fully reducing, unlike call-by-name reduction of the original Krivine machine),
that is more efficient than interpreters based on $\alpha$-conversion and capture-avoiding substitution.

I found this paper to be very clear; the presented abstract machine state transitions can directly be translated into code.
Overall it is an excellent read!

[^1]: P. Crégut, "Strongly reducing variants of the Krivine abstract machine", Higher-Order Symb Comput, vol. 20, no. 3, pp. 209–230, Nov. 2007, doi: 10.1007/s10990-007-9015-z.

[^2]: Á. GARCÍA-PÉREZ and P. NOGUEIRA, "The full-reducing Krivine abstract machine KN simulates pure normal-order reduction in lockstep: A proof via corresponding calculus", Journal of Functional Programming, vol. 29, p. e7, 2019. doi:10.1017/S0956796819000017


# Usage

This repository is designed as a library.
A minimal complete demo project that uses this library and reduces expressions provided on the commandline is available at https://github.com/stfnw/lambda-calculus-abstract-machine-kn-cli.

Build:

```
cargo build
```

Build and test while also showing outputs:

```
cargo test -- --nocapture
```

An example output for doing some math with church numerals (taken from the test):

```
$ cargo test -- --nocapture
   Compiling lambda_calculus_full_reducing_krivine_machine v0.1.0 (lambda-calculus-full-reducing-krivine-machine)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 1.63s
     Running unittests src/lib.rs (target/debug/deps/lambda_calculus_full_reducing_krivine_machine-71ed9f8a9e85d28f)

running 3 tests

...

comment (($MUL $FOUR) $THREE)
parsed  (((λa. (λb. (λc. (λd. ((a (b c)) d))))) (λa. (λb. (a (a (a (a b))))))) (λa. (λb. (a (a (a b))))))
        (((λ (λ (λ (λ ((3 (2 1)) 0))))) (λ (λ (1 (1 (1 (1 0))))))) (λ (λ (1 (1 (1 0))))))
reduced (λa. (λb. (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))
        (λ (λ (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))))))

comment (($ADD (($MUL $TWO) $THREE)) $FOUR)
parsed  (((λa. (λb. (λc. (λd. ((a c) ((b c) d)))))) (((λa. (λb. (λc. (λd. ((a (b c)) d))))) (λa. (λb. (a (a b))))) (λa. (λb. (a (a (a b))))))) (λa. (λb. (a (a (a (a b)))))))
        (((λ (λ (λ (λ ((3 1) ((2 1) 0)))))) (((λ (λ (λ (λ ((3 (2 1)) 0))))) (λ (λ (1 (1 0))))) (λ (λ (1 (1 (1 0))))))) (λ (λ (1 (1 (1 (1 0)))))))
reduced (λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))
        (λ (λ (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))))

comment (($ADD $FOUR) (($MUL $THREE) $TWO))
parsed  (((λa. (λb. (λc. (λd. ((a c) ((b c) d)))))) (λa. (λb. (a (a (a (a b))))))) (((λa. (λb. (λc. (λd. ((a (b c)) d))))) (λa. (λb. (a (a (a b)))))) (λa. (λb. (a (a b))))))
        (((λ (λ (λ (λ ((3 1) ((2 1) 0)))))) (λ (λ (1 (1 (1 (1 0))))))) (((λ (λ (λ (λ ((3 (2 1)) 0))))) (λ (λ (1 (1 (1 0)))))) (λ (λ (1 (1 0))))))
reduced (λa. (λb. (a (a (a (a (a (a (a (a (a (a b))))))))))))
        (λ (λ (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))))

...
```
