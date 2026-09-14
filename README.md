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
Here boundedness means that one positive real radius `R` satisfies `‖x‖ ≤ R` for
every interior point; unboundedness means that exterior points exist with `R < ‖x‖`
for every real `R`. The checked standard regions expose these statements directly as
`exists_standardInside_radius` and `exists_standardOutside_beyond`.
`Bornology.IsBounded` in library interfaces is mathlib's name for this same boundedness.

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
and polygon challenge statements against their proofs. The finite separation challenge
also checks the attributed dependency. The common-boundary challenge states Sections 1–3
for an arbitrary continuous circle embedding, with explicit radius bounds. These checks
certify the named milestones; they do not certify the still-unfinished Jordan theorem. Lean Beam is used locally
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
Finite polygonal separation is now supplied by the attributed finite-only dependency
closure of [Álvaro Begué's collar/parity proof](vendor/README.md), ported and checked
on this toolchain. Its general Jordan and Schoenflies assembly is excluded. The adapter
accepts our actual simple polygons, including collinear consecutive edges.
The standard deep regions are open, disjoint, and exhaust the curve's complement;
both regions are nonempty, the inside is bounded, the outside is unbounded, and the
curve is their common boundary. The inner polygon and final connectivity and
simple-connectivity arguments remain open. Nearest-segment lemmas and the circle-parametrization bridge are also checked.
Section 3's equal-distance estimate is proved for the actual polygon arcs, using their
common-shadow endpoint restriction. Generic local squares can be chosen to avoid every
vertex at a prescribed standard scale. Finite plane-graph face cycles are checked;
the polygon-square overlay is now constructed and proved to remain connected after
deleting any vertex. On either polygon side, it supplies a simple polygonal cell whose
boundary passes through the prescribed local curve vertex. The cell meets both cut
arcs away from that vertex, and a path around the punctured cell supplies the required
square-boundary connector. Its balanced point has a standard part deep on the chosen
side in any prescribed neighborhood. This completes the published Section 3.
The independently stated result is `Verification.curve_common_boundary` in
`Verification/CommonBoundarySolution.lean`; it assumes only continuity and injectivity
of the circle map.

Lemma 3's narrow rectangles now have checked metric estimates and explicit polygonal
boundaries. Their finite overlay remains connected after deleting any vertex. It
produces an actual internal inner cell around each prescribed standard interior point,
whose closed interior avoids the extended curve and whose boundary is in the curve's
monad. Every standard compact set off the curve uniformly avoids the entire rectangle
and shortest-connection construction zone. The rectangle arrangement now includes
actual shortest connections from all its vertices. Every corner of the resulting
inner cell, including corners created by new intersections, has a shortest connection
already in the drawing, so that connection avoids the cell interior. These connections
are uniformly infinitesimal and stay in the outer polygon's inside until reaching
their feet. The ring argument showing that
one inner polygon contains **all** standard interior points remains open.

The [Verso blueprint](blueprint/README.md) builds locally and links completed declarations
to the remaining proof obligations. Rendered files are generated, not committed.

After the full proof is complete, a second phase will refactor the development into
more native nonstandard statements and reusable transfer/metaprogramming tools, with
the aim of extracting components suitable for mathlib PRs.
