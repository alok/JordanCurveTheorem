# Source correspondence and proof obligations

The primary source is Vladimir Kanovei and Michael Reeken, *A nonstandard proof of
the Jordan curve theorem*, Real Analysis Exchange 24(1), 161–170,
[published scan](https://www.maths.ed.ac.uk/~v1ranick/jordan/jor.pdf).
The [1996 arXiv version](https://arxiv.org/abs/math/9608204) is a secondary source.
The published argument adds a common-boundary argument absent from the earlier version.

This ledger describes the whole intended proof. An open row is an unproved obligation,
not a theorem available for downstream use. The final independently stated target is
`Verification/JordanChallenge.lean`; it has no solution module yet.

| Source step | Lean development | Status |
| --- | --- | --- |
| Nonstandard extension and transfer | `Reeken/Nonstandard/Ultrapower.lean`: quotient by an ultrafilter, internal predicates, Boolean connectives, existential and universal quantifiers | Proved |
| Hyperfinite extrema and induction | `Reeken/Nonstandard/Hyperfinite.lean` | Proved |
| Unlimited indices | `Hyperfinite.lean`, `Saturation.lean` | Proved |
| Countable saturation and overspill | `Reeken/Nonstandard/Saturation.lean`: diagonal construction over a free ultrafilter on naturals | Proved |
| Compact standard parts | `Reeken/Nonstandard/Metric.lean` | Proved |
| Infinitesimal continuity and inverse continuity | `Metric.lean`: compact injective maps preserve and reflect nearness | Proved |
| Standard shadows and appreciable separation | `Reeken/Nonstandard/Shadow.lean`: closed shadow of any internal set; positive uniform distance outside its shadow | Proved |
| Finite polygonal Jordan theorem used by the paper | Polygonal separation, two path components, common boundary, bounded inside, simple connectivity | Open |
| Lemma 1(i) | A sufficiently fine inscribed internal polygon has unlimited vertex count and infinitesimal parameter gaps | Open |
| Lemma 1(ii) | Two-sided infinitesimal approximation of the original curve | Open |
| Lemma 1(iii) | Exactly one of the two arcs between near points is infinitesimally small | Open |
| Lemma 2, metric inequality | `Reeken/Geometry/Segments.lean`: an intersection of two segments permits a replacement edge no longer than the longer original edge | Proved |
| Lemma 2, construction | Hyperfinite sampling, internal loop cutting, termination, preservation of parameter order and mesh | Open |
| Standard inside/outside | Appreciable distance to the approximating polygon gives disjoint open standard regions exhausting the complement | Open |
| Published Section 3 | Each curve point lies on the boundary of both regions; local square and polygonal cell construction | Open |
| Lemma 3 | Internal inner polygon using narrow rectangles and shortest boundary connections; ring and crosscut argument | Open |
| Connectivity and simple connectivity | Transfer finite polygon results through the inner polygon | Open |
| Exterior | Inversion and path connectivity; unboundedness | Open |
| Final theorem | A continuous embedding of the unit circle has two complementary regions with the stated boundary and connectivity properties | Open |

## Mathematical corrections and representation choices

The published polygon condition `(†)` prints `Pᵢ = K(tᵢ)` only for `1 ≤ i < n`,
although the last vertex must also lie on the parametrized curve. The formal condition
will require this for every vertex, including the last. Subsequent uses of the last
vertex depend on that intended condition.

The arXiv discussion includes adjacent overlapping edges among the degeneracies to
remove during loop cutting. The formal construction must handle these too; distinct
nonadjacent crossings alone do not imply simplicity.

The paper takes the polygonal Jordan theorem as known. This project includes it in
its scope and will not introduce it as an axiom. Similarly, compactness, transfer,
saturation, or internal induction must be derived in the model actually implemented.

## Independent verification

`Verification/NSAChallenge.lean` states three foundation claims using ordinary
sequences, metrics, compactness, and ultrafilters, without importing project definitions.
`Verification/NSASolution.lean` supplies the corresponding proofs. Comparator is
configured to compare them and invoke Nanoda. Challenge holes are intentionally
confined to challenge modules; they are not imported by any proof module.

The axiom audit traverses project declarations, including private helpers, and accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Official `leanchecker --fresh`
replays declarations through Lean's kernel; Nanoda is a separate implementation.
These are different checks, and CI reports them separately.
