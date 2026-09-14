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
| Internal images and standard curve intersections | `Reeken/Nonstandard/Images.lean`: image transfer and compact standard-part extraction at an internal intersection | Proved |
| Initial inscribed mesh | `Reeken/Geometry/UniformMesh.lean`: explicit consecutive sampling and two-sided uniform approximation | Proved |
| Initial mesh in the nonstandard model | `Reeken/Nonstandard/MeshApproximation.lean`: exact shadow and infinitesimal endpoints for every internal edge | Proved |
| Finite polygonal separation used by the paper | `Geometry/PolygonSeparation.lean` adapts the attributed finite collar/parity proof in `vendor/Schoenflies`; open connected regions, common boundary, bounded inside, unbounded outside; path connectivity in `Verification/SeparationSolution.lean` | Proved |
| Finite polygonal simple connectivity | Contractibility of all interior loops, beyond finite separation and crosscuts | Open |
| Circle-parametrization bridge | `Geometry/CircleParametrization.lean`: continuous embeddings of the plane unit circle give the simple-loop representation with exactly the same image | Proved |
| Simple-loop parameter identification | `Geometry/SimpleLoop.lean`, `Nonstandard/Loop.lean`: equality or identified endpoints; forward and closing gap control | Proved |
| Conditions (†), (‡) | `Geometry/InscribedPolygon.lean`: strictly ordered parameters, all vertices on the curve, half-circle conditions, cyclic gaps, maxima, and telescoping sum | Defined with proved elementary properties |
| An initial polygon satisfying (†), (‡) | `Geometry/UniformPolygon.lean`, `Nonstandard/InitialPolygon.lean`: explicit equally spaced samples, infinitesimal maximum edge, and exact shadow | Proved |
| Lemma 1(i) | `Nonstandard/PolygonRegularity.lean`: uniformly infinitesimal gaps, unlimited vertex count, first parameter near zero and last near one | Proved |
| Lemma 1(ii) | `Geometry/PolygonApproximation.lean`, `Nonstandard/PolygonApproximation.lean`: two-sided approximation by a single positive infinitesimal, and exact standard shadow | Proved |
| Lemma 1(iii) | `Nonstandard/PolygonArcs.lean`, `Nonstandard/EdgePoints.lean`, `Nonstandard/PointArcs.lean`: exactly one of the two cuts between near points lies in their monad, first for vertices and then for arbitrary points on edges | Proved |
| Lemma 2, metric inequality | `Reeken/Geometry/Segments.lean`: an intersection of two segments permits a replacement edge no longer than the longer original edge | Proved |
| Lemma 2, construction | `Geometry/PolygonSlice.lean`, `PolygonDeletion.lean`, `MinimalPolygon.lean`, `SimplePolygon.lean`, `Nonstandard/SimpleApproximation.lean`: two shortcut deletions, finite minimization, crossing and backtracking exclusion, infinitesimal simple approximation | Proved |
| Transfer of a given internal separation | `Reeken/Nonstandard/Regions.lean`: deep regions are open and disjoint and exhaust the complement of the boundary shadow; finite separation is an explicit input | Proved |
| Standard inside/outside for a Jordan curve | `Nonstandard/StandardRegions.lean`: instantiated finite separation, open disjoint regions, exact complement coverage, connected sets crossing the two regions meet the curve | Proved |
| Bounded inside and nonempty unbounded outside | `Geometry/ExteriorBounds.lean`, `Nonstandard/RegionBounds.lean`: one standard square uniformly encloses all polygon interiors; its exterior lies deeply outside | Proved |
| Nonempty standard inside | Requires the common-boundary construction | Open |
| Shortest boundary connections | `Geometry/NearestSegments.lean`, `PolygonTopology.lean`: compact nearest feet, uniqueness along nondegenerate segments, exclusion of isolated interior crossings, compact and path-connected polygon traces | Proved |
| Published Section 3 | Each curve point lies on the boundary of both regions; local square and polygonal cell construction | Open |
| Lemma 3 | Internal inner polygon using narrow rectangles and shortest boundary connections; ring and crosscut argument | Open |
| Connectivity and simple connectivity | Transfer finite polygon results through the inner polygon | Open |
| Exterior connectivity | Inversion and path connectivity; unboundedness is already in `RegionBounds.lean` | Open |
| Final theorem | A continuous embedding of the unit circle has two complementary regions with the stated boundary and connectivity properties | Open |

## Mathematical corrections and representation choices

The published polygon condition `(†)` prints `Pᵢ = K(tᵢ)` only for `1 ≤ i < n`,
although the last vertex must also lie on the parametrized curve. The formal condition
will require this for every vertex, including the last. Subsequent uses of the last
vertex depend on that intended condition.

The arXiv discussion includes adjacent overlapping edges among the degeneracies to
remove during loop cutting. The formal construction must handle these too; distinct
nonadjacent crossings alone do not imply simplicity.

The construction now excludes adjacent overlaps using `dist_le_max_of_adjacent_overlap`.
Termination is expressed by finite minimization of the vertex count at each index.
The two explicit deletion operations contradict minimality whenever a forbidden short
chord exists. This is the well-ordering form of the paper's finite loop-cutting induction;
it does not assume simplicity or a separation theorem.

The paper takes the polygonal Jordan theorem as known. This project includes it in
its scope and does not introduce it as an axiom. Its finite separation and crosscut
foundation is the 36-module transitive closure of `Schoenflies.PrePolygonSep` at
`alonamaloh/schoenflies-lean@05a43d29cde026618777db3d4e4316204ccca237`, by Álvaro Begué,
under Apache 2.0. See `vendor/README.md` for attribution, scope, and compatibility edits.
The general Jordan and Schoenflies assembly modules are excluded. This reuse supplies
the finite theorem assumed by the source, not the nonstandard limiting argument. Similarly, compactness, transfer,
saturation, or internal induction must be derived in the model actually implemented.

The basic ultrapower, transfer, and metric constructions accept arbitrary ultrafilters.
`countable_saturation_of_le_atTop` works for any ultrafilter on naturals that contains
all tails. `hyperfilter ℕ` supplies a chosen instance of this condition; its particular
choice is mathematically irrelevant to the proof.

## Independent verification

`Verification/NSAChallenge.lean` states three foundation claims using ordinary
sequences, metrics, compactness, and ultrafilters, without importing project definitions.
`Verification/NSASolution.lean` supplies the corresponding proofs. Comparator is
configured to compare them and invoke Nanoda. Challenge holes are intentionally
confined to challenge modules; they are not imported by any proof module.

`Verification/MeshChallenge.lean` independently writes out the sampled segments and
states the mesh-shadow result entirely in terms of sequences and standard metric
estimates. It is checked against `MeshSolution.lean` by a separate Comparator invocation.

`Verification/PolygonChallenge.lean` independently states Lemma 2 using parameter arrays,
explicit segments, forbidden intersections, and ordinary sequence estimates for the shadow.
`PolygonSolution.lean` supplies its proof; `polygon.json` requests Comparator and Nanoda.

`Verification/SeparationChallenge.lean` states finite polygonal separation with explicit
cyclic segments, ordinary open path-connected sets, boundedness, and frontiers.
`SeparationSolution.lean` proves it from the attributed finite proof; `separation.json`
requests Comparator and Nanoda without trusting project definitions in the statement.

The axiom audit traverses both `Reeken` and `Schoenflies` declarations, including private helpers, and accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Official `leanchecker --fresh`
replays declarations through Lean's kernel; Nanoda is a separate implementation.
These are different checks, and CI reports them separately.
