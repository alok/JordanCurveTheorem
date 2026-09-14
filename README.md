# JordanCurveTheorem

A Lean 4 formalization of Vladimir Kanovei and Michael Reeken's nonstandard proof of
the Jordan curve theorem, including the nonstandard machinery and finite polygonal
foundation.

**The full theorem is proved in Lean.** The public declaration is
[`Reeken.jordanCurveTheorem`](Reeken/Jordan.lean).
[`Verification/JordanSolution.lean`](Verification/JordanSolution.lean) proves the
unchanged independent [full challenge](Verification/JordanChallenge.lean).
The subsequent work is to improve the NSA interfaces and extract reusable tooling.

For every continuous injective map of the unit circle into the real plane, the
complement consists of two nonempty disjoint open path-connected regions. The inside
is bounded and simply connected, the outside is unbounded, and the original curve
is the common boundary. No polygonal separation, ear-existence, or finite contraction
hypothesis remains in the final theorem.

The primary source is the [published paper](https://www.maths.ed.ac.uk/~v1ranick/jordan/jor.pdf),
*A nonstandard proof of the Jordan curve theorem*, **Real Analysis Exchange 24**(1),
161–170. The [1996 arXiv version](https://arxiv.org/abs/math/9608204) is a secondary
source; the published version includes the common-boundary argument.

## Checking the proof

- Lean `v4.33.1`
- mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`
- [Lean build, audit, and fresh kernel replay](https://github.com/alok/JordanCurveTheorem/actions/workflows/lean.yml)
- [Comparator and Nanoda](https://github.com/alok/JordanCurveTheorem/actions/workflows/comparator.yml)

```sh
lake exe cache get
lake --wfail build Reeken Verification.JordanSolution
lake env lean scripts/Audit.lean
lake env leanchecker --fresh Reeken
```

The audit checks every project and vendored declaration, including private helpers
and declarations in other namespaces. It accepts only `propext`, `Classical.choice`,
and `Quot.sound`. Proof modules contain no `sorry`, additional axioms, or
`native_decide`. The intentional holes occur only in independent challenge modules,
which are not imported by the proofs.

The Linux verification workflow builds pinned Comparator, lean4export, Nanoda, and
Landrun. Comparator compares independently stated challenge and solution modules,
then checks exported proofs with Nanoda as a second kernel implementation. It runs
under Landrun with the documented AF_UNIX restrictions. Ten targets cover the NSA
foundations, mesh approximation, simple polygon approximation, finite separation,
common boundaries, inside connectivity, both regions' connectivity, triangle
contraction and convex attachment, internal diagonal existence, and the full Jordan
theorem. Workflow results report these checks separately from Lean's fresh replay.

Lean Beam has also been used locally for incremental diagnostics and speculative
proof checks. The checked sources and repeatable kernel commands are the evidence
for proof correctness.

## Reading the development

| Part | Entry points |
| --- | --- |
| Full theorem and circle formulation | [`Reeken/Jordan.lean`](Reeken/Jordan.lean), [`CircleParametrization.lean`](Reeken/Geometry/CircleParametrization.lean) |
| Ultrapowers, transfer, hyperfinite objects, saturation | [`Ultrapower.lean`](Reeken/Nonstandard/Ultrapower.lean), [`Hyperfinite.lean`](Reeken/Nonstandard/Hyperfinite.lean), [`Saturation.lean`](Reeken/Nonstandard/Saturation.lean) |
| Standard parts and shadows | [`Metric.lean`](Reeken/Nonstandard/Metric.lean), [`Shadow.lean`](Reeken/Nonstandard/Shadow.lean) |
| Lemma 1 and the actual simple approximation of Lemma 2 | [`PolygonApproximation.lean`](Reeken/Nonstandard/PolygonApproximation.lean), [`PolygonArcs.lean`](Reeken/Nonstandard/PolygonArcs.lean), [`SimpleApproximation.lean`](Reeken/Nonstandard/SimpleApproximation.lean) |
| Published Section 3: common boundaries | [`CommonBoundary.lean`](Reeken/Nonstandard/CommonBoundary.lean) |
| Lemma 3: one inner polygon containing all standard inside points | [`RingContainment.lean`](Reeken/Nonstandard/RingContainment.lean) |
| Connectivity of both regions | [`InsideConnectivity.lean`](Reeken/Nonstandard/InsideConnectivity.lean), [`OutsideConnectivity.lean`](Reeken/Nonstandard/OutsideConnectivity.lean) |
| Internal diagonals, ears, and finite contraction | [`PolygonDiagonal.lean`](Reeken/Geometry/PolygonDiagonal.lean), [`PrePolygonDiagonal.lean`](Reeken/Geometry/PrePolygonDiagonal.lean), [`PolygonEars.lean`](Reeken/Geometry/PolygonEars.lean) |
| Contraction of arbitrary continuous loops through the NSA construction | [`LoopContraction.lean`](Reeken/Nonstandard/LoopContraction.lean), [`SimplyConnected.lean`](Reeken/Nonstandard/SimplyConnected.lean) |

The nonstandard extension uses `Filter.Germ` over an ultrafilter. Generic transfer
results work with arbitrary ultrafilters; the countable saturation construction uses
a free ultrafilter on the naturals. The geometric development instantiates this with
mathlib's chosen `hyperfilter ℕ`. It does not assume a separate nonstandard axiom.

The paper assumes the Jordan theorem for polygons. This project supplies finite
separation through the attributed finite-only dependency from
[Álvaro Begué's collar/parity formalization](vendor/README.md). Its general Jordan and
Schoenflies assembly is excluded. The contraction development here constructs
internal diagonals, permits collinear vertices, minimizes the number of spanned
boundary edges to obtain an ear, and contracts by induction with a strict vertex-count
decrease. Parity cancellation identifies the closed regions of each actual deletion.

For simple connectivity of the original curve's inside, every compact loop lies in
one finite inner polygon whose **entire closed inside** stays in the standard inside.
The finite contraction can therefore run along its own polygon boundary while
remaining inside the original curve. This covers arbitrary continuous loops,
including self-intersecting ones.

The exterior argument uses the outer rectangle face and the dual infinitesimal-barrier
proof in place of the paper's inversion step. The
[source correspondence](docs/source-map.md) records this variation, the polygon
normalization details, and the published paper's indexing correction.

`Bornology.IsBounded` is mathlib's interface for ordinary boundedness. The standard
regions also expose explicit real-radius statements:
`exists_standardInside_radius` bounds every inside point by one positive radius,
and `exists_standardOutside_beyond` supplies outside points beyond every real radius.

The [Verso blueprint](blueprint/README.md) links the proof's mathematical steps to
checked declarations. Rendered files are generated locally rather than committed.
Project work is tracked in [Linear](https://linear.app/aloksingh/project/jordancurvetheorem-8681f02f7dfd).

## Reusable NSA tooling

The first complete proof precedes the requested refactoring. Subsequent work will
make more theorem interfaces native to the nonstandard development, replace repeated
quotient/transfer plumbing with checked metaprogramming, and isolate interfaces that
could be proposed to mathlib. The fixed independent theorem and kernel checks remain
the validation boundary throughout that work.
