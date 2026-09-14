import Reeken.Geometry.DrawingCorners
import Reeken.Geometry.NearestSpokeDrawing
import Mathlib.Analysis.InnerProductSpace.Convex

/-! # Every corner of an arrangement cell has an existing shortest connection

Corners of a cell lie on an old vertex or on an added connection. On the interior
of a shortest connection, its foot is uniquely nearest. Thus even the new corners
created where a connection meets a rectangle side have their entire shortest
connection already present in the arrangement.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

def spokeSet (vertices : Finset Plane) (foot : Plane → Plane) : Set Plane :=
  ⋃ x ∈ vertices, segment ℝ x (foot x)

theorem isCompact_spokeSet (vertices : Finset Plane) (foot : Plane → Plane) :
    IsCompact (spokeSet vertices foot) :=
  vertices.finite_toSet.isCompact_biUnion (fun x _ ↦ isCompact_segment x (foot x))

theorem vertex_mem_spokeSet {vertices : Finset Plane} (foot : Plane → Plane) {x : Plane}
    (hx : x ∈ vertices) : x ∈ spokeSet vertices foot :=
  mem_iUnion₂.mpr ⟨x, hx, left_mem_segment ℝ _ _⟩

/-- Shortening any one of the drawn nearest connections stays in the same family. -/
theorem nearest_segment_subset_spokeSet {C : Set Plane} {vertices : Finset Plane}
    {foot : Plane → Plane} (hfoot : ∀ x, IsNearest C x (foot x)) {x : Plane}
    (hx : x ∈ spokeSet vertices foot) : segment ℝ x (foot x) ⊆ spokeSet vertices foot := by
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
  have hfx : foot x = foot v := by
    by_cases hxv' : x = v
    · exact congrArg foot hxv'
    · exact (hfoot v).unique_on_segment hxv hxv' (hfoot x).1
        ((hfoot x).2 (foot v) (hfoot v).1)
  intro y hy
  rw [hfx] at hy
  exact mem_iUnion₂.mpr ⟨v, hv,
    (convex_segment v (foot v)).segment_subset hxv (right_mem_segment ℝ _ _) hy⟩

/-- Every vertex of a cell polygon has its nearest connection in the drawn family,
including new vertices formed by crossings with rectangle sides. -/
theorem polygon_vertex_nearest_segment_subset_spokes {G : Graph Plane Piece} [G.Finite]
    (hd : Graph.IsDrawing G segmentDrawing) {vertices : Finset Plane}
    (hvertices : V(G) ⊆ (vertices : Set Plane)) {C : Set Plane} {foot : Plane → Plane}
    (hfoot : ∀ x, IsNearest C x (foot x)) {m : ℕ} (Q : ClosedPolygon m)
    (hQ : Q.carrier ⊆ Graph.pointSet G segmentDrawing ∪ spokeSet vertices foot)
    (i : ZMod (m + 3)) :
    segment ℝ (Q.vertex i) (foot (Q.vertex i)) ⊆ spokeSet vertices foot := by
  apply nearest_segment_subset_spokeSet hfoot
  rcases polygon_vertex_mem_drawing_vertices_or_closed hd Q
      (isCompact_spokeSet vertices foot).isClosed hQ i with hi | hi
  · exact vertex_mem_spokeSet foot (hvertices hi)
  · exact hi

end Reeken.Geometry
