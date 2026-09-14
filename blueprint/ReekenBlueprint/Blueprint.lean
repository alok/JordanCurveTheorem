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

The full Jordan theorem remains open in this development. The nodes below separate
checked Lean declarations from mathematical obligations. The primary source is
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

:::theorem "polygon_simply_connected" (tags := "open")
Every loop in the interior of a finite simple plane polygon contracts there.
This obligation remains open beyond {uses "polygon_jordan"}[].
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

:::theorem "common_boundary" (tags := "open")
Every point of the loop is a boundary point of both standard regions. The published
local-square construction uses {uses "lemma2"}[], {uses "lemma1iii"}[],
{uses "polygon_jordan"}[], {uses "generic_squares"}[], {uses "local_cell"}[],
and {uses "equidistant_bound"}[]. The square-boundary connector between the two cut arcs
remains open; {uses "deep_regions"}[] transfers the resulting point.
:::

:::theorem "inner_polygon" (tags := "open")
There is an internal inner polygon containing every standard interior point and whose
interior avoids the extended loop. The rectangle arrangement and crosscut argument use
{uses "lemma1ii"}[], {uses "lemma1iii"}[], {uses "polygon_jordan"}[], and
{uses "common_boundary"}[]. The full construction remains open.
:::

:::theorem "connectivity" (tags := "open")
The inside is path connected and simply connected; the outside is path connected and
unbounded. The unboundedness is checked in {uses "region_bounds"}[]. Connectivity remains
open: transfer through {uses "inner_polygon"}[], {uses "polygon_simply_connected"}[], and
inversion should establish it.
:::

:::theorem "jordan" (tags := "open")
Every continuous injective map of the unit circle into the real plane has exactly the
two complementary regions specified above. The fixed independent challenge also asks
for their common boundary and the interior's simple connectivity. It depends on
{uses "common_boundary"}[] and {uses "connectivity"}[]. There is no solution module yet.
:::

The requested refactoring into more native nonstandard statements and reusable
metaprogramming begins only after the full checked proof is complete.

{blueprint_graph}
{blueprint_summary}
