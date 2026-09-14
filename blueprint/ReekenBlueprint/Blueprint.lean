import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Reeken

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Kanovei–Reeken: Jordan Curve Theorem" =>

The full Jordan theorem is proved. The nodes below connect its checked Lean
declarations to the mathematical argument. The primary source is
Kanovei and Reeken's published article in *Real Analysis Exchange* 24(1), 161–170.
Its finite polygonal Jordan theorem is included in this project's scope.

# Nonstandard foundations

:::definition "ultrapower" (lean := "Reeken.NSA.Star")
The nonstandard extension is a quotient of sequences by an ultrafilter.
Internal predicates are represented by indexed predicates; logical connectives
and quantifiers have proved transfer rules.
:::

:::theorem "saturation" (lean := "Reeken.NSA.countable_saturation_of_le_atTop")
Every countable family of internal conditions with the finite intersection property
has a simultaneous realization. This holds for any ultrafilter on naturals containing
all tails, using {uses "ultrapower"}[].
:::

:::proof "saturation"
At each index choose a witness to the longest satisfiable finite prefix bounded by
that index. The prefix lengths tend to infinity along the ultrafilter.
:::

:::theorem "standard_part" (lean := "Reeken.NSA.compact_standard_part")
An internal point in the extension of a compact set is near a standard point of that
set. The point lives in {uses "ultrapower"}[].
:::

:::proof "standard_part"
Push the ultrafilter through a representative sequence and use compactness.
:::

:::theorem "closed_shadow" (lean := "Reeken.NSA.isClosed_shadow")
The standard shadow of any internal metric set is closed, using {uses "saturation"}[].
:::

:::proof "closed_shadow"
Saturation identifies shadow membership with approximation at every positive standard
scale. Failure of membership gives a uniform positive distance bound.
:::

# Inscribed polygons

:::definition "admissible" (lean := "Reeken.Geometry.InscribedPolygon")
The vertices lie on the loop in strictly increasing parameter order in the half-open
unit interval. Every forward gap is at most one half, and the span from the first
to the last parameter is at least one half. Self-intersections are allowed here.
:::

:::theorem "initial_polygon" (lean := "Reeken.NSA.exists_initial_polygon")
An explicit uniform mesh gives an {uses "admissible"}[] polygon with infinitesimal
edges and the loop as its shadow.
:::

:::proof "initial_polygon"
Use equally spaced parameters and uniform continuity on the compact parameter interval.
:::

:::theorem "lemma1i" (lean := "Reeken.NSA.vertex_count_unlimited")
An {uses "admissible"}[] polygon with infinitesimal edges has unlimited vertex count.
Its largest parameter gap is infinitesimal, its first parameter is near zero, and
its last parameter is near one. Inverse continuity uses {uses "standard_part"}[].
:::

:::proof "lemma1i"
Near image points have near parameters or lie near the identified endpoints.
The half-circle conditions select the appropriate alternative. The cyclic gaps sum to one.
:::

:::theorem "lemma1ii" (lean := "Reeken.NSA.polygon_infinitesimal_hausdorff")
There is one positive infinitesimal bounding the approximation in both directions,
using {uses "lemma1i"}[] and {uses "saturation"}[].
:::

:::proof "lemma1ii"
Uniform continuity bounds the distance from the curve to a sampled vertex; an edge's
length bounds its distance to the curve. Saturation supplies one infinitesimal bound.
:::

:::theorem "lemma1iii" (lean := "Reeken.NSA.exactly_one_point_arc_small")
Exactly one of the two polygon arcs between near points lies in their monad.
This uses {uses "lemma1i"}[], {uses "lemma1ii"}[], and {uses "standard_part"}[].
:::

:::proof "lemma1iii"
First use compact inverse continuity at vertices. Two distinct standard shadow points
exclude both arcs being small. Moving the cuts within their infinitesimal edges
preserves the small-arc assertion, including the same-edge case.
:::

:::theorem "lemma2" (lean := "Reeken.NSA.exists_simple_polygon")
Every simple continuous loop has an internal simple inscribed polygon with infinitesimal
edges and precisely that loop as shadow. Start with {uses "initial_polygon"}[] and
preserve {uses "admissible"}[]; use {uses "lemma1i"}[] to exclude low vertex counts.
:::

:::proof "lemma2"
Retain either the inner or the outer parameter arc according to its span. Both explicit
shortcut deletions preserve admissibility and the maximum-edge bound. Minimize the
finite vertex count at each index. Any nonadjacent crossing or adjacent backtracking
would give a shorter admissible polygon, contradicting minimality.
:::

# Remaining planar geometry and assembly

:::theorem "polygon_jordan" (lean := "Reeken.Geometry.InscribedPolygon.Simple.isSeparating")
A finite simple plane polygon separates into bounded inside and unbounded outside,
both open and connected, with the polygon as their common boundary.
:::

:::proof "polygon_jordan"
Adapt the actual vertex and edge conditions to the finite collar/parity proof by
Álvaro Begué, retained under Apache 2.0 in the vendored finite dependency closure.
Collinear consecutive edges are normalized. General Jordan assembly is excluded.
:::

:::theorem "path_mesh_homotopy" (lean := "Reeken.Geometry.exists_meshPath_homotopy")
Every continuous path in an open set is homotopic there, with endpoints fixed, to
an actual finite polygonal mesh path. Self-intersections are allowed.
:::

:::proof "path_mesh_homotopy"
Affine formulas on the finitely many closed mesh intervals agree at common endpoints,
so their pasting is continuous. Uniform continuity gives uniform convergence to the
original path. Compactness of the path range gives a positive distance margin inside
the open set; the straight homotopy to a sufficiently close mesh stays within that margin.
:::

:::theorem "triangle_contraction" (lean := "Reeken.Geometry.contractibleSpace_triangle_closed_inside")
The closed inside of every three-vertex simple polygon is contractible.
:::

:::proof "triangle_contraction"
Supporting half-planes contain all bounded complementary components. Each triangle
edge lies on a supporting line of the convex hull of its vertices, so finite separation
identifies the closed inside with that hull. Convexity supplies the contraction.
:::

:::theorem "convex_attachment" (lean := "Reeken.Geometry.contractibleSpace_union_of_segment_inter")
Attaching a closed convex piece along one segment to a closed contractible set
preserves contractibility.
:::

:::proof "convex_attachment"
Truncated distance from one endpoint gives a continuous retraction onto the segment.
The straight deformation inside the convex piece agrees with the identity on the
intersection, so closed-set pasting makes a deformation of the union onto the rest.
:::

:::theorem "triangle_crosscut" (lean := "Reeken.Geometry.contractible_closed_inside_of_triangle_crosscut")
A diagonal cutting off a triangle reduces closed-inside contractibility to the
remaining polygon, using {uses "triangle_contraction"}[] and {uses "convex_attachment"}[].
:::

:::proof "triangle_crosscut"
The existing finite crosscut theorem identifies the two cells. Their closed interiors
cover the parent and meet exactly on the cutting segment. Apply convex attachment
to the triangle's closed interior.
:::

:::theorem "exposed_corner" (lean := "Reeken.Geometry.exists_vertex_inward_bisector")
Every finite simple polygon has a vertex whose inward bisector enters its inside.
:::

:::proof "exposed_corner"
A vertex of maximal norm is strictly exposed: the squared-distance identity gives
a linear height strictly below its maximum at every other vertex. Opposite collar
sectors contain the bisector and its negative. The negative direction is beyond the
supporting line and outside; distinctness of the two components puts the bisector inside.
:::

:::theorem "interior_straight_cut" (lean := "Reeken.Geometry.exists_vertex_to_nonincident_edge_cut")
A vertex joins a nonincident edge by a straight segment whose open part lies inside.
The far endpoint may lie between vertices.
:::

:::proof "interior_straight_cut"
Extend the ray from {uses "exposed_corner"}[]. Boundedness gives a point beyond the
inside. Minimize the boundary-intersection parameter on the intervening compact
interval. Before this first hit the ray stays inside. Independence of the corner's
two rays rules out either incident edge as the first hit.
:::

:::theorem "empty_neighbor_triangle" (lean := "Reeken.Geometry.empty_corner_triangle_inside")
At a strictly supported corner, if the neighbor triangle contains no other polygon
vertex, the triangle's inside and closed inside lie in the corresponding polygonal sets.
:::

:::proof "empty_neighbor_triangle"
A supporting height forces a segment entering the triangle to cross an adjacent side.
Polygon simplicity therefore excludes every polygon edge from an empty triangle's
interior. A small point on the inward bisector belongs to both insides, so connectedness
puts the entire triangle inside the polygon. This uses {uses "exposed_corner"}[].
:::

:::theorem "empty_triangle_diagonal" (lean := "Reeken.Geometry.empty_corner_base_inside")
For a polygon with more than three vertices, the base of an empty neighbor triangle
misses the polygon except at its ends. At a strictly supported corner it is an
internal diagonal.
:::

:::proof "empty_triangle_diagonal"
Signed-area coordinates show that a transverse crossing of the base enters the
triangle interior, contradicting {uses "empty_neighbor_triangle"}[]. A collinear
edge through the open base must contain both base ends; simplicity would then make
those nonadjacent vertices adjacent, a contradiction.
:::

:::theorem "empty_triangle_deletion" (lean := "Reeken.Geometry.exists_smaller_polygon_of_empty_corner")
Deleting the apex of an empty neighbor triangle yields an actual polygon with
strictly fewer vertices and no new vertices.
:::

:::proof "empty_triangle_deletion"
Use the disjoint diagonal from {uses "empty_triangle_diagonal"}[] to check every
edge intersection in the shortened cyclic vertex family. Normalize any collinear
corners. The normalization induction preserves the vertex-count bound and vertex-set
inclusion, so the resulting closed polygon remains strictly smaller.
:::

:::theorem "ear_contraction_induction" (lean := "Reeken.Geometry.contractible_closed_inside_of_internal_ears")
If every nontriangular polygon has an internal ear, every polygon's closed inside
is contractible. The geometric hypothesis is discharged by {uses "polygon_ears"}[].
:::

:::proof "ear_contraction_induction"
The edge list of the actual deletion in {uses "empty_triangle_deletion"}[] gives a
parity sum: the diagonal occurs twice and cancels. The triangle and shortened polygon
have disjoint open insides; their closed insides cover the original and meet exactly
along the diagonal. Apply {uses "convex_attachment"}[] and the normalization count
bound, then strong induction with {uses "triangle_contraction"}[] as base case.
:::

:::theorem "internal_diagonal" (lean := "Reeken.Geometry.exists_internal_diagonal")
Every nontriangular simple polygon has an internal diagonal between existing,
nonadjacent vertices.
:::

:::proof "internal_diagonal"
At the corner in {uses "exposed_corner"}[], use {uses "empty_triangle_diagonal"}[]
when the neighbor triangle is empty. Otherwise choose a vertex of maximal signed-area
height in that triangle. A line through it parallel to the base cuts off a smaller
triangle whose interior has no polygon edge. Its unit bisector agrees with the
original corner's, placing it inside. The segment to the selected vertex is internal.
:::

:::theorem "polygon_ears" (lean := "Reeken.Geometry.exists_internal_ear")
Every nontriangular simple polygon has an internal ear.
:::

:::proof "polygon_ears"
Extend {uses "internal_diagonal"}[] to collinear corners by normalization; if the
carrier becomes a triangle, an extra edge vertex joins the opposite corner.
Minimize the number of boundary edges spanned by an internal diagonal. Closing that
arc gives a polygon inside the original region. A span greater than two would yield
an internal diagonal of this smaller polygon and contradict minimality. A span of
two is an internal triangle.
:::

:::theorem "polygon_simply_connected" (lean := "Reeken.Geometry.contractibleSpace_closed_inside")
The closed inside of every finite simple plane polygon is contractible.
:::

:::proof "polygon_simply_connected"
Apply {uses "ear_contraction_induction"}[] using {uses "polygon_ears"}[].
Normalization preserves the strict decrease in vertex count. The base case is
{uses "triangle_contraction"}[]. These closed contractions suffice for the standard
inside because its compact-loop extraction includes the polygon boundary.
:::

:::theorem "deep_regions" (lean := "Reeken.NSA.deep_union_of_separation")
An internal separation into open disjoint regions transfers to standard deep regions
that exhaust the complement of the boundary shadow, using {uses "closed_shadow"}[].
The separation is an explicit hypothesis of this intermediate theorem.
:::

:::proof "deep_regions"
An appreciable ball avoiding the boundary stays on one side by connectedness.
Use the ultrafilter alternative to choose the side containing its standard center.
:::

:::theorem "standard_regions" (lean := "Reeken.NSA.standardRegions_union")
The actual {uses "lemma2"}[] approximation and {uses "polygon_jordan"}[] give two
open disjoint standard regions covering the curve's complement via {uses "deep_regions"}[].
:::

:::proof "standard_regions"
Apply finite separation eventually, using the unlimited vertex count, and then transfer.
:::

:::theorem "region_bounds" (lean := "Reeken.NSA.not_isBounded_standardOutside")
The standard inside is bounded; the standard outside is nonempty and unbounded.
:::

:::proof "region_bounds"
One standard square encloses every inscribed polygon. The square's connected unbounded
exterior lies in each polygon's outside, and lies deeply there at every standard point.
:::

:::theorem "arc_common_shadow" (lean := "Reeken.NSA.common_arc_shadow_subset")
The two long polygon arcs have only their two limiting cut endpoints in their common
shadow. Parameter extraction uses {uses "lemma1i"}[] and {uses "standard_part"}[].
:::

:::proof "arc_common_shadow"
Move each edge point to its incident vertex, extract compact parameter standard parts,
and use the loop's injectivity with its sole endpoint identification.
:::

:::theorem "equidistant_bound" (lean := "Reeken.NSA.polygon_equidistant_uniform_bound")
Balanced points on a compact set avoiding the cut endpoints have one positive standard
distance bound from the polygon, using {uses "arc_common_shadow"}[] and {uses "saturation"}[].
:::

:::proof "equidistant_bound"
If simultaneous proximity were arbitrarily small, saturation would give two near
arc points and a compact standard part in their common shadow. Equal nearest-foot
distances turn this exclusion into a bound for the entire polygon.
:::

:::theorem "generic_squares" (lean := "Reeken.NSA.exists_generic_polygon_squares")
At a prescribed standard scale, choose each square radius to avoid all polygon vertices.
The cut vertices lie on opposite sides, and every square boundary lies in one compact annulus.
:::

:::proof "generic_squares"
Exclude the finite set of vertex sup-distances, and use convergence of the selected cut vertices.
:::

:::theorem "finite_cells" (lean := "Reeken.Geometry.exists_polygon_of_bounded_face")
A bounded face of a finite 2-connected polygonal drawing is the interior of an actual
simple polygon whose boundary lies in the drawing.
:::

:::proof "finite_cells"
Use the attributed finite face-cycle theorem, which grows the graph by ears and applies
the finite crosscut theorem at arbitrary cut points. Normalize the cycle's polygonal carrier.
:::

:::theorem "local_cell" (lean := "Reeken.Geometry.InscribedPolygon.Simple.exists_clipped_polygon")
On either side of the polygon, clipping by the local square gives a simple polygonal
cell whose boundary contains the chosen vertex. The cell boundary lies on the polygon
or square, and its points off the polygon lie on the chosen side.
:::

:::proof "local_cell"
Both cut arcs cross the square at distinct points. Subdivide to make these crossings
vertices. Puncturing each closed carrier leaves it connected, and one common point
survives, so the finite overlay remains connected after any vertex deletion.
The finite face family and {uses "finite_cells"}[] then supply a cell through the
prescribed boundary point.
:::

:::theorem "square_connector" (lean := "Reeken.Geometry.InscribedPolygon.Simple.exists_square_connector")
The {uses "local_cell"}[] supplies a connected square-boundary segment meeting both
cut arcs, on the chosen polygon side away from the original polygon.
:::

:::proof "square_connector"
A closed curve cannot run through a free arc endpoint. Hence the cell meets each cut
arc away from their common local vertex. Join these points around the punctured cell
and use first and last contact to extract a subpath on the square boundary.
:::

:::theorem "common_boundary" (lean := "Reeken.NSA.frontier_standardInside")
Every point of the loop is a boundary point of both standard regions. The published
local-square construction uses {uses "lemma2"}[], {uses "lemma1iii"}[],
{uses "polygon_jordan"}[], {uses "generic_squares"}[], {uses "local_cell"}[],
and {uses "equidistant_bound"}[].
:::

:::proof "common_boundary"
Choose {uses "square_connector"}[] in a compact annulus avoiding both standard cut
points. A balanced point has appreciable distance from the polygon. Its compact
standard part belongs deeply to the chosen side in an arbitrarily small neighborhood
of the curve point. Apply the same construction to the other side. The open disjoint
partition in {uses "standard_regions"}[] gives equality of both frontiers with the curve.
:::

:::theorem "rectangle_zone" (lean := "Reeken.NSA.eventually_disjoint_innerConstructionZone")
Every compact standard set off the curve avoids the entire family of narrow rectangles
and all shortest connections from their points to the polygon. The internal covering
uses {uses "lemma1ii"}[].
:::

:::proof "rectangle_zone"
A rectangle point and its nearest foot are within the maximum edge length plus four
times the infinitesimal padding. Uniform proximity places the construction zone's
shadow in the curve; compactness turns disjoint shadows into uniform avoidance.
:::

:::theorem "inner_cell" (lean := "Reeken.NSA.exists_internal_inner_cell")
For each standard inside point there is an actual internal inner polygon containing
that point deeply. Its closed inside avoids the extended curve, and its boundary
shadow is contained in the curve. This uses {uses "rectangle_zone"}[] and {uses "finite_cells"}[].
:::

:::proof "inner_cell"
The affine images of squares give the prescribed rectangle boundaries. Each meets the
polygon twice, so the overlay remains connected after any vertex deletion. Choose its
bounded face at the prescribed point. The face closure stays outside each rectangle
interior, and the rectangles cover the extended curve.
:::

:::theorem "inner_spoke_cell" (lean := "Reeken.NSA.exists_internal_inner_spoke_cell")
The inner cell can be constructed with a nearest-foot map whose corner connections
are uniformly infinitesimal, avoid the cell interior, and remain in the outer polygon
until their feet. Its closed inside avoids the extended curve and contains the chosen
point deeply. This uses {uses "rectangle_zone"}[] and {uses "finite_cells"}[].
:::

:::proof "inner_spoke_cell"
Attach shortest connections to every vertex of the rectangle drawing. The drawing
remains connected after deleting any vertex. Away from old vertices a straight-edge
drawing is locally one segment, so each corner of the new cell is either an old
vertex or lies on an added connection. Uniqueness of the nearest foot along that
connection places the corner's whole shortest connection in the drawing. The face
interior avoids every drawn segment. Transfer and the uniform rectangle error give
the internal cell and its infinitesimal connections.
:::

:::theorem "inner_polygon" (lean := "Reeken.NSA.exists_internal_inner_polygon")
One internal inner polygon contains every standard inside point deeply, and its closed
inside avoids the extended loop. Its boundary shadow is contained in the original curve.
:::

:::proof "inner_polygon"
Start with {uses "inner_spoke_cell"}[]. Bisect the inner polygon's edges to make them
infinitesimal, preserving its carrier and crossing parity. Close each edge against the
small outer arc of {uses "lemma1iii"}[]. Each resulting barrier is infinitesimal, so two
standard points off the curve see the same parity. Summing cancels the connections;
the remaining closed outer-arc chain has constant parity in the outer polygon's inside
by {uses "polygon_jordan"}[]. Thus every standard inside point has the inner polygon's
inside parity. Boundary avoidance promotes membership to deep membership.
:::

:::theorem "inside_connected" (lean := "Reeken.NSA.isPathConnected_standardInside")
The standard inside is path connected.
:::

:::proof "inside_connected"
For two standard inside points, {uses "inner_polygon"}[] supplies a finite representative
whose inside contains both and whose closed inside misses the original curve. The finite
inside is path connected by {uses "polygon_jordan"}[], and belongs to the standard inside
because the two standard regions are disjoint and open. Its paths are the required paths.
:::

:::theorem "outside_connected" (lean := "Reeken.NSA.isPathConnected_standardOutside")
The standard outside is path connected.
:::

:::proof "outside_connected"
Take the outer face of the rectangle arrangement from {uses "rectangle_zone"}[].
Its closed outside misses the extended curve and its boundary is infinitesimally
close to the inscribed polygon. Repeat the barrier cancellation of {uses "inner_polygon"}[]
on the finite outside. One distant standard point fixes the outside parity, so every
standard outside point lies deeply outside this same outer polygon. Finite exterior
paths give the required paths. This is the dual construction in place of the paper's inversion.
:::

:::theorem "compact_loop_reduction" (lean := "Reeken.NSA.isSimplyConnected_standardInside_of_polygon")
If every finite simple polygon has simply connected inside, the standard inside is
simply connected. The completed proof uses the stronger closed-region extraction below.
:::

:::proof "compact_loop_reduction"
The range of any continuous loop is compact. Through {uses "inner_polygon"}[], one
finite polygon contains the entire range in its inside, and its whole inside belongs
to the standard inside. The explicit finite simple-connectivity hypothesis contracts
the loop there. This handles arbitrary continuous loops, including self-intersecting ones.
:::

:::theorem "closed_compact_loop_reduction" (lean := "Reeken.NSA.isSimplyConnected_standardInside_of_closed_polygon")
Contractibility of every finite closed polygonal inside also suffices to prove
simple connectivity of the standard inside. The finite input is {uses "polygon_simply_connected"}[].
:::

:::proof "closed_compact_loop_reduction"
The finite extraction from {uses "inner_polygon"}[] retains the whole closed inside
within the standard inside. Thus a contraction can meet the finite polygon's boundary
while staying inside the original curve. Apply this to the compact range of any loop.
:::

:::theorem "connectivity" (lean := "Reeken.NSA.isSimplyConnected_standardInside")
The standard inside is simply connected. Both complementary regions are path connected.
:::

:::proof "connectivity"
Combine {uses "closed_compact_loop_reduction"}[] with the finite contraction theorem
{uses "polygon_simply_connected"}[]. Path connectivity is proved in
{uses "inside_connected"}[] and {uses "outside_connected"}[].
:::

:::theorem "jordan" (lean := "Reeken.jordanCurveTheorem")
Every continuous injective map of the unit circle into the real plane has two nonempty
open path-connected complementary regions, a bounded simply connected inside, an
unbounded outside, and the curve as their common boundary.
:::

:::proof "jordan"
Use the actual simple polygon approximation and its standard regions. Combine
{uses "common_boundary"}[] with {uses "connectivity"}[] and the established radius
bounds. `Verification.JordanSolution` proves the unchanged independent full challenge.
:::

The requested refactoring into more native nonstandard statements and reusable
metaprogramming follows this first complete proof; the independent theorem and kernel checks remain fixed.

{blueprint_graph}
{blueprint_summary}
