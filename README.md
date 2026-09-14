# JordanCurveTheorem

Lean 4 formalization of the nonstandard proof of the Jordan curve theorem by
Vladimir Kanovei and Michael Reeken, including the nonstandard and polygonal foundations.

**Work in progress. The Jordan curve theorem is not yet proved in this repository.**
Completed modules must contain actual Lean proofs. An unfinished target is never promoted
to an axiom or hidden behind a structure field that assumes the conclusion.

The primary source is the
[published paper](https://www.maths.ed.ac.uk/~v1ranick/jordan/jor.pdf),
*Real Analysis Exchange* **24**(1), 161–170. Its common-boundary argument and
simple-connectivity discussion extend the
[1996 arXiv version](https://arxiv.org/abs/math/9608204).
The source paper assumes the Jordan theorem for polygons; proving that foundation
is part of this project's scope.

The intended conclusion is for **every continuous injective map of the circle into
the real plane**: two nonempty open path-connected complementary regions, a bounded
simply connected interior, an unbounded exterior, and the curve as their common boundary.

## Development

- Lean `v4.33.1`
- Upstream mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`
- [Linear project](https://linear.app/aloksingh/project/jordancurvetheorem-8681f02f7dfd)
- [Completion issue](https://linear.app/aloksingh/issue/ALOK-911)

```sh
lake exe cache get
lake build
```

The nonstandard extension is built from `Filter.Germ` over an ultrafilter. This gives
actual quotient objects and proved transfer rules, with no new foundational axioms.
