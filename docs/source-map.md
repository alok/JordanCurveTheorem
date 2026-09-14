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
| Nonempty standard inside | `Nonstandard/CommonBoundary.lean`: every ball at a curve point meets the inside | Proved |
| Shortest boundary connections | `Geometry/NearestSegments.lean`, `PolygonTopology.lean`: compact nearest feet, uniqueness along nondegenerate segments, exclusion of isolated interior crossings, compact and path-connected polygon traces | Proved |
| Section 3, equal-distance step | `Geometry/Equidistant.lean`, `Nonstandard/CompactSeparation.lean`, `ArcShadow.lean`, `PolygonEquidistant.lean`: the arcs' common shadow contains only their cut endpoints; balanced points on an avoiding compact set have one positive standard distance bound from the full polygon | Proved |
| Standard part of a constructed cell point | `Nonstandard/DeepStandardPart.lean`, `BoundaryConnector.lean`: a compact connector meeting the two arcs on one side gives a standard deep point; all hypotheses are instantiated in `CommonBoundary.lean` | Proved |
| Local square scale and genericity | `Geometry/SquareAnnulus.lean`, `Nonstandard/CutVertices.lean`, `PolygonSquares.lean`: prescribed cut parameters, generic radii avoiding every vertex, opposite-side cut vertices, and a fixed compact annulus | Proved |
| Compact standard loop inclusion | `Nonstandard/CompactDeep.lean`: pointwise deep inclusion of a compact set implies inclusion of its entire internal extension | Proved |
| Extracting a boundary subpath | `Geometry/BoundarySubpath.lean`: first/last contacts with two closed pieces yield a connecting subpath in the third boundary piece; its interior avoids both original pieces | Proved |
| Finite cell boundaries | `Geometry/PolygonCells.lean`: a bounded face of a finite 2-connected polygonal plane graph has an actual simple polygon boundary; uses the attributed finite face-cycle proof | Proved |
| The two square crossings | `Geometry/ArcConnectivity.lean`, `ArcIntersection.lean`, `SquareCrossings.lean`: the two polygon arcs are path connected, meet exactly at their cut vertices, and cross the local square at distinct points | Proved |
| The polygon-square graph | `Geometry/MarkedOverlay.lean`, `PolygonSquareOverlay.lean`, `DrawingDeletion.lean`, `LoopPuncture.lean`, `SquareTwoConnected.lean`: retain old vertices and marked crossings, construct the finite drawing, and prove connectivity after every vertex deletion | Proved |
| The local cell through the chosen vertex | `Geometry/FiniteFaces.lean`, `SquareFaces.lean`, `LocalCells.lean`: finiteness of the face family, a face on either chosen side with the vertex in its boundary, and an actual clipped simple polygon | Proved |
| Square-boundary connector | `Geometry/ArcEndpoint.lean`, `ArcParametrization.lean`, `SquareConnector.lean`: the clipped cell meets both cut arcs away from their endpoints; a path around the punctured cell supplies a connector on the chosen side | Proved |
| Published Section 3 | `Nonstandard/CommonBoundary.lean`: both frontiers equal the original curve, using the actual local cells, balanced connector points, and compact standard parts; direct continuous-circle formulation in `Verification/CommonBoundarySolution.lean` | Proved |
| Lemma 3, narrow rectangles | `Geometry/EdgeRectangles.lean`, `PolygonRectangles.lean`, `RectangleBoundary.lean`: the prescribed dimensions, neighborhood coverage, short connections, and affine square images giving actual polygon boundaries | Proved |
| Lemma 3, uniform avoidance | `Nonstandard/RectangleApproximation.lean`: the whole construction zone has shadow in the curve; all standard compact sets off the curve eventually avoid it | Proved |
| Lemma 3, nearest connection location | `Geometry/NearestRegions.lean`: a shortest connection stays in its starting component until its boundary foot | Proved |
| Lemma 3, rectangle overlay | `Geometry/BoundaryCrossings.lean`, `PolygonFamilyOverlay.lean`, `RectangleOverlay.lean`: every thin rectangle crosses the polygon twice, and the whole finite drawing is 2-connected | Proved |
| Lemma 3, inner cell at a chosen point | `Geometry/RectangleCells.lean`, `Nonstandard/InnerCell.lean`: an actual simple inner polygon contains the prescribed standard point deeply, its closed inside avoids the extended curve, and its boundary shadow is contained in the curve | Proved |
| Lemma 3, drawing the shortest connections | `Geometry/SpokeConnectivity.lean`, `AttachedSegments.lean`, `NearestSpokeDrawing.lean`, `RectangleSpokes.lean`: attach the finite family, including coincident feet and degenerate segments, while retaining 2-connectivity and the uniform construction-zone bound | Proved |
| Lemma 3, connections at every cell corner | `Geometry/DrawingCorners.lean`, `SpokeFeet.lean`, `InnerFace.lean`, `SpokeCell.lean`: new cell corners lie at old vertices or on drawn connections; uniqueness of the nearest foot puts their shortest connections in the drawing, outside the cell interior | Proved |
| Lemma 3, internal cell with connections | `Nonstandard/InnerSpokeCell.lean`: an actual internal polygon and nearest-foot map, with uniformly infinitesimal corner connections avoiding its inside, and the prescribed standard point deeply inside | Proved |
| Lemma 3, simultaneous containment | `Nonstandard/RingContainment.lean`: infinitesimal edge barriers, small outer arcs, and cancellation of finite crossing parity put every standard inside point deeply in one actual inner polygon | Proved |
| Inside path connectivity | `Nonstandard/InsideConnectivity.lean`: choose a finite representative of the inner polygon containing both standard points, whose connected inside misses the original curve | Proved |
| Compact-loop reduction | `Nonstandard/LoopContraction.lean`: every compact inside set lies in a finite inner polygon; arbitrary continuous loop contractions transfer, with finite polygonal simple connectivity an explicit hypothesis | Proved reduction; finite hypothesis open |
| Exterior connectivity | `Geometry/OuterCells.lean`, `Nonstandard/OuterCell.lean`, `OuterContainment.lean`, `OuterPolygon.lean`, `OutsideConnectivity.lean`: actual outer cell, infinitesimal-barrier cancellation, and finite exterior paths | Proved |
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
foundation is the 47-module transitive closure of `Schoenflies.FaceCyclesLand` (including
`Schoenflies.PrePolygonSep`) at
`alonamaloh/schoenflies-lean@05a43d29cde026618777db3d4e4316204ccca237`, by Álvaro Begué,
under Apache 2.0. See `vendor/README.md` for attribution, scope, and compatibility edits.
Four additional finite excerpts supply square coordinates and graph traces; the extraction
ledger records their source modules and exact included declarations.
The general Jordan and Schoenflies assembly modules are excluded. This reuse supplies
the finite theorem assumed by the source, not the nonstandard limiting argument. Similarly, compactness, transfer,
saturation, or internal induction must be derived in the model actually implemented.

The basic ultrapower, transfer, and metric constructions accept arbitrary ultrafilters.
`countable_saturation_of_le_atTop` works for any ultrafilter on naturals that contains
all tails. `hyperfilter ℕ` supplies a chosen instance of this condition; its particular
choice is mathematically irrelevant to the proof.

The published Section 3 displays the equal-distance condition as
`d = d(E, α) − d(E, β)`. The surrounding sentence and contradiction argument require
`d = d(E, α) = d(E, β)`; subtraction would make `d` zero at an equidistant point.
The formal equal-distance lemmas use the intended equality.

In Lemma 3's second kind of ring domain, the printed common-endpoint condition
`Cₖ = Cₖ₊₁` refers to the feet `Cₖ′ = Cₖ₊₁′`. Consecutive vertices of the inner
simple polygon are distinct. The formal nearest-segment lemmas distinguish initial
vertices from boundary feet, and allow different connections to have the same foot.

The finite rectangle arrangement draws connections from every subdivided arrangement
vertex, a finite superset of the paper's selected inner rectangle vertices and crossings.
Connections from outside points stay outside until their feet, and the complete drawing
still lies in the same infinitesimal construction zone. Degenerate connections are removed
from the edge list while their points remain in the carrier. A cell corner created by a
new intersection lies on an already drawn connection; strict convexity gives its unique
nearest foot and shows that the shortened connection is already in the drawing.

The simultaneous-containment proof realizes the paper's infinitesimal-barrier argument
through finite crossing parity, rather than classifying all ring domains. Each refined
inner edge is closed against the small outer arc supplied by Lemma 1(iii). The outer
endpoints are nearest outer vertices; replacing a nearest trace point by an incident
vertex adds at most one infinitesimal outer edge. Every resulting closed chain lies
in an infinitesimal ball, so standard points off the curve see the same parity. When
these equalities are summed, the connecting segments cancel modulo two. The remaining
closed chain lies on the outer polygon and has constant parity on its connected
inside. Thus every standard inside point has the chosen cell point's inner-polygon
parity. `RingContainment.lean` proves this implication and the full Lemma 3 witness.
`AnnulusOverlay.lean` separately constructs the two-connected annular drawing, but a
three-kind classification of its domains is not claimed or used by the parity proof.

There is a representation detail in this step: the normalized `ClosedPolygon` can
merge collinear consecutive edges, so its edge lengths need not remain infinitesimal.
`FineChains.lean` repeatedly bisects those segments, preserving the carrier, the closed
chain identity, and crossing parity. It supplies the required infinitesimal edges
without assuming that normalization preserves their lengths.

For exterior connectivity, the formal proof uses the outer rectangle face and repeats
the infinitesimal-barrier argument on the finite polygon's connected outside. This is
the dual of the inner-polygon construction. The published paper instead invokes
inversion. The formal route proves the same exterior-connectivity conclusion without
an unproved assertion that inversion swaps the standard regions. It does not claim to
formalize that inversion step literally.

`LoopContraction.lean` handles arbitrary continuous loops, including self-intersecting
ones: their ranges are compact and hence lie in one finite inner polygon whose whole
inside belongs to the standard inside. The reduction takes finite polygonal simple
connectivity as an explicit hypothesis. That finite theorem is still open, so the
reduction must not be reported as an unconditional simple-connectivity proof.

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

`Verification/CommonBoundaryChallenge.lean` states the common-boundary conclusion for
every continuous injective map of the plane unit circle, with nonempty disjoint open
regions covering the complement and explicit real-radius bounds. Its statement uses
no project definitions. `CommonBoundarySolution.lean` proves it from the actual simple
approximation and the published Section 3 construction; `common-boundary.json` requests
Comparator and Nanoda. Connectivity is not asserted by this intermediate result.

`Verification/InsideConnectedChallenge.lean` strengthens that independent circle-map
statement with path connectivity of the bounded region. Its solution uses the proved
Lemma 3 through `isPathConnected_standardInside`; `inside-connected.json` requests
Comparator and Nanoda. Outside path connectivity is proved by the next milestone; inside simple connectivity
remains open.

`Verification/ComplementConnectedChallenge.lean` further asserts path connectivity
of both complementary regions. `ComplementConnectedSolution.lean` proves this direct
circle-embedding statement, with explicit radii; `complement-connected.json` requests
Comparator and Nanoda. The fixed `JordanChallenge.lean` additionally requires simple
connectivity and still has no solution module.

The axiom audit traverses all declarations by their defining module (`Reeken` or `Schoenflies`),
including private helpers and declarations in other namespaces such as `Graph`, and accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Official `leanchecker --fresh`
replays declarations through Lean's kernel; Nanoda is a separate implementation.
These are different checks, and CI reports them separately.
