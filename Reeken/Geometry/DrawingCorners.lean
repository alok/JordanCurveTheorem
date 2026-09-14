import Schoenflies.OverlayGraph
import Schoenflies.Realization
import Schoenflies.Graph.Degree

/-! # Corners of a polygon carried by a straight-edge drawing

Away from the vertices, a finite straight-edge drawing is locally a single
segment. Consequently, a polygon carried by that drawing and an additional
closed set can have new corners only on the additional set.
-/

open Set Metric Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem isStraightAt_drawing_of_not_vertex {G : Graph Plane Piece} [G.Finite]
    (hd : Graph.IsDrawing G segmentDrawing) {x : Plane}
    (hx : x ∈ Graph.pointSet G segmentDrawing) (hxV : x ∉ V(G)) :
    IsStraightAt (Graph.pointSet G segmentDrawing) x := by
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp (hx.resolve_left hxV)
  have hlink : G.IsLink e e.1 e.2 := by
    simpa only [segmentDrawing, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      using (hd.edge_param he).2.2
  have hxleft : x ≠ e.1 := fun h ↦ hxV (h ▸ hlink.left_mem)
  have hxright : x ≠ e.2 := fun h ↦ hxV (h ▸ hlink.right_mem)
  have hxseg : x ∈ openSegment ℝ e.1 e.2 :=
    mem_openSegment_of_ne_left_right (Ne.symm hxleft) (Ne.symm hxright)
      (by simpa only [edgeArc_segmentDrawing, Piece.seg] using hxe)
  let other := V(G) ∪ ⋃ d ∈ E(G) \ {e}, Graph.edgeArc segmentDrawing d
  have hfinite : (E(G) \ {e}).Finite := (Graph.finite_edgeSet G).sdiff
  have hother : IsClosed other := (Graph.finite_vertexSet G).isClosed.union
    (hfinite.isClosed_biUnion (fun d hd' ↦ (hd.isCompact_edgeArc hd'.1).isClosed))
  have hxother : x ∉ other := by
    rintro (hx' | hx')
    · exact hxV hx'
    · obtain ⟨d, hd', hxd⟩ := mem_iUnion₂.mp hx'
      exact hd'.2 (hd.unique_edge_at he hd'.1 hxV hxe hxd).symm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hother.isOpen_compl x hxother
  refine ⟨e.1, e.2, hxseg, r, hr, ?_⟩
  rintro y ⟨hyball, hy⟩
  rcases hy with hyV | hyE
  · exact (hball hyball (Or.inl hyV)).elim
  · obtain ⟨d, hd', hyd⟩ := mem_iUnion₂.mp hyE
    by_cases hde : d = e
    · subst d
      simpa only [edgeArc_segmentDrawing, Piece.seg] using hyd
    · exact (hball hyball (Or.inr (mem_iUnion₂.mpr ⟨d, ⟨hd', hde⟩, hyd⟩))).elim

theorem polygon_vertex_mem_drawing_vertices_or_closed {G : Graph Plane Piece} [G.Finite]
    (hd : Graph.IsDrawing G segmentDrawing) {m : ℕ} (Q : ClosedPolygon m)
    {S : Set Plane} (hS : IsClosed S) (hQ : Q.carrier ⊆ Graph.pointSet G segmentDrawing ∪ S)
    (i : ZMod (m + 3)) : Q.vertex i ∈ V(G) ∪ S := by
  by_cases hiS : Q.vertex i ∈ S
  · exact Or.inr hiS
  by_cases hiV : Q.vertex i ∈ V(G)
  · exact Or.inl hiV
  exfalso
  have hiG := (hQ Q.vertex_mem_carrier).resolve_right hiS
  obtain ⟨a, b, hab, r, hr, hstraight⟩ := isStraightAt_drawing_of_not_vertex hd hiG hiV
  obtain ⟨s, hs, havoid⟩ := Metric.isOpen_iff.mp hS.isOpen_compl (Q.vertex i) hiS
  apply (Q.isCornerAt_vertex i).2
  refine ⟨a, b, hab, min r s, lt_min hr hs, ?_⟩
  rintro x ⟨hxb, hxQ⟩
  rcases hQ hxQ with hxG | hxS
  · exact hstraight ⟨(ball_subset_ball (min_le_left _ _)) hxb, hxG⟩
  · exact (havoid ((ball_subset_ball (min_le_right _ _)) hxb) hxS).elim

end Reeken.Geometry
