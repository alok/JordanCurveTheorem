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

The current development also proves hyperfinite extrema and induction, countable
saturation and overspill, compact standard parts, preservation and reflection of
infinitesimal nearness for compact embeddings, closedness of standard shadows, and
the segment-length estimate used in loop cutting. See the
[source correspondence and remaining obligations](docs/source-map.md).

```sh
lake env lean scripts/Audit.lean
lake env leanchecker --fresh Reeken
```

CI runs a full build and axiom audit. A separate Linux workflow builds pinned
Comparator, lean4export, Nanoda, and Landrun, then checks the independent NSA
challenge statements against their proofs. This checks the named foundation results;
it does not certify the still-unfinished Jordan theorem. Lean Beam is used locally
for incremental diagnostics and speculative proof checks.

The current polygon development establishes the paper's Lemma 1(i)–(iii) for
arbitrary admissible inscribed polygon families: unlimited vertex count, uniformly
infinitesimal parameter gaps, endpoint behavior, and a single positive infinitesimal
bounding the approximation in both directions. Exactly one of the two arcs between
near points lies in their monad, including cuts at arbitrary points on edges. An
explicit initial polygon family satisfies the required parameter conditions.
Lemma 2 is also proved: the two shortcut deletions preserve the parameter conditions
and edge bound, finite minimization gives termination, and the resulting polygon has
neither nonadjacent crossings nor adjacent backtracking. The independent polygon
challenge states this approximation without project definitions.
Finite polygonal separation and the later boundary, inner-polygon, and connectivity
arguments remain to be proved.

After the full proof is complete, a second phase will refactor the development into
more native nonstandard statements and reusable transfer/metaprogramming tools, with
the aim of extracting components suitable for mathlib PRs.
