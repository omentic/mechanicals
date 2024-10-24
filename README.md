# the mechanicals

Various implementations of the lambda calculus (and friends).

The code here is hopefully pretty readable: but makes heavy use of quasiquoting, and contracts. \
For an introduction to quasiquoting, see [*Explaining Lisp's quoting without getting tangled*](quasiquoting). For an introduction to contracts, see [*Simple contracts on functions*](https://docs.racket-lang.org/guide/contract-func.html).

* untyped
  * [ ] lc.rkt: The untyped lambda calculus.
  * [ ] ski.rkt: The SKI combinator calculus.
  * [ ] iota.rkt, jot.rkt, zot.rkt: Implementations of Chris Barker's combinator languages.
  * [ ] aviary.rkt: Various combinators and constructions of equivalence.
* simple
  * [x] stlc.rkt: The simply-typed lambda calculus.
  * [x] ext.rkt: Simple extensions. Sums, products, lists, ascryptions.
  * [x] fix.rkt: General recursion.
  * [x] rec.rkt: Iso-recursive types.
  * [x] ref.rkt: References. No garbage collection. Nonterminating.
* research
  * [x] hor.rkt: Higher-order im/predicative references. Terminating.
  * [x] dll.rkt: Doubly-linked lists via sums, products, ascryption, recursive types, and impredicative references. Terminating?
  * [x] levels.rkt: Higher-order im/predicative references with an algebraic level system. Terminating?


[quasiquoting]: https://cadence.moe/blog/2022-10-17-explaining-lisp-quoting-without-getting-tangled
