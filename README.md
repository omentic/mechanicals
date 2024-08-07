# the mechanicals

Various implementations of the lambda calculus (and friends).

The code here is hopefully pretty readable: but makes heavy use of quasiquoting.
For an introduction, see [*Explaining Lisp's quoting without getting tangled*](quasiquoting).

* [~] LC: The untyped lambda calculus.
* [x] STLC: The simply-typed lambda calculus.
* [x] STLC-ext: Simple extensions. Sums, products, lists, ascryptions.
* [x] STLC-fix: General recursion.
* [x] STLC-rec: Iso-recursive types.
* [ ] STLC-sub: Subtyping. Structural records, intersective unions, implicit typeclasses, ⊤, ⊥.
* [x] STLC-ref: References.
* [x] STLC-pred: Higher-order *predicative* references. Terminating.
* [x] STLC-imp: Higher-order *impredicative* references. Terminating.
* [x] STLC-dll: Doubly-linked lists via sums, products, ascryption, recursive types, and impredicative references. Terminating?
* [ ] STLC-rc: References with reference counting.
* [ ] STLC-gc: References with a tracing garbage collector.
* [ ] STLC-own: References with first-class ownership, Rust-style.
* [ ] STLC-lent: References with second-class ownership.
* [ ] STLC-dep: Dependent types with normalization by evaluation.
* [~] SKI: The SKI combinator calculus.
* [~] Iota, Jot, Zot: Implementations of Chris Barker's languages.
* [~] Aviary: Various combinators and constructions of equivalence.


[quasiquoting]: https://cadence.moe/blog/2022-10-17-explaining-lisp-quoting-without-getting-tangled
