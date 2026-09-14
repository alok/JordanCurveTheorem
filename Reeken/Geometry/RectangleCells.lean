import Reeken.Geometry.RectangleOverlay
import Reeken.Geometry.PolygonCells
import Reeken.Geometry.SquareFaces

/-! # An actual inner polygonal cell in the rectangle arrangement

A point of the polygon interior outside every covering rectangle lies in a
bounded arrangement face. Its closure misses the rectangle interiors, hence the
original polygon and every set covered by those interiors. This gives an inner
simple polygon around the chosen point. The assertion that every other standard
interior point lies in the same cell requires the subsequent ring argument.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

theorem face_subset_compl_closed_of_frontier_subset {D : Set Plane} (hD : IsClosed D)
    (hboundary : frontier D ⊆ Graph.pointSet G drawing) {z : Plane}
    (hz : z ∈ Graph.exterior G drawing) (hzD : z ∉ D) :
    Graph.face G drawing z ⊆ Dᶜ := by
  intro x hx hxD
  have hxi : x ∈ interior D := by
    by_contra h
    have hxfr : x ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨hxD, h⟩
    exact Graph.face_subset_exterior G drawing z hx (hboundary hxfr)
  obtain ⟨y, hyF, hyD⟩ := exists_frontier_crossing isPreconnected_connectedComponentIn hD
    hx (Graph.mem_face hz) hxi hzD
  exact Graph.face_subset_exterior G drawing z hyF (hboundary hyD)

theorem closure_face_subset_compl_interior {D : Set Plane} (hD : IsClosed D)
    (hboundary : frontier D ⊆ Graph.pointSet G drawing) {z : Plane}
    (hz : z ∈ Graph.exterior G drawing) (hzD : z ∉ D) :
    closure (Graph.face G drawing z) ⊆ (interior D)ᶜ := by
  simpa only [closure_compl] using
    closure_mono (face_subset_compl_closed_of_frontier_subset hD hboundary hz hzD)

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

/-- The finite rectangle arrangement supplies an actual inner simple polygon.
The closure of its inside misses every open covering rectangle. -/
theorem Simple.exists_rectangle_cell (hp : p.Simple) (hn : 2 ≤ p.n) {ε : ℝ} (hε : 0 < ε)
    {a b : Fin (p.n + 1)} (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b))
    {z : Plane} (hz : z ∈ inside p.trace) (hzR : z ∉ p.rectangleCover ε) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      z ∈ inside Q.carrier ∧ Q.carrier ⊆ inside p.trace ∧
      inside Q.carrier ⊆ inside p.trace ∧
      closure (inside Q.carrier) ⊆ (p.openRectangleCover ε)ᶜ ∧
      Q.carrier ⊆ ⋃ j, frontier (p.closedRectangle ε j) := by
  obtain ⟨q, points, _, hd, htwo, hpoint, _⟩ := hp.exists_rectangle_overlay p hn hε hfar
  let G := overlayGraph (p.pieces ++ polygonFamilyPieces q) points
  have hzext : z ∈ Graph.exterior G segmentDrawing := by
    intro h
    rw [hpoint] at h
    rcases h with hzC | hzR'
    · exact hz.1 hzC
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hzR'
      exact hzR (mem_iUnion.mpr ⟨j, (isClosed_closedEdgeRectangle _ _ _ _).frontier_subset hj⟩)
  have hCsub : p.trace ⊆ Graph.pointSet G segmentDrawing := by rw [hpoint]; exact subset_union_left
  have hface : Graph.face G segmentDrawing z ⊆ inside p.trace := face_subset_inside hCsub hz
  have hclosure : closure (Graph.face G segmentDrawing z) ⊆ (p.openRectangleCover ε)ᶜ := by
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    have hboundary : frontier (p.closedRectangle ε j) ⊆ Graph.pointSet G segmentDrawing := by
      rw [hpoint]
      exact fun y hy ↦ Or.inr (mem_iUnion.mpr ⟨j, hy⟩)
    have hzj : z ∉ p.closedRectangle ε j := fun h ↦ hzR (mem_iUnion.mpr ⟨j, h⟩)
    exact closure_face_subset_compl_interior (isClosed_closedEdgeRectangle _ _ _ _)
      hboundary hzext hzj hx (p.openRectangle_subset_interior ε j hj)
  obtain ⟨m, Q, hfrontier, hinside, hQsub⟩ := exists_polygon_of_bounded_face hd
    (fun e _ ↦ by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _) htwo hzext
    ((hp.isSeparating hn).isBounded_inside.subset hface)
  have hQoff : Disjoint Q.carrier p.trace := by
    rw [Set.disjoint_left]
    intro x hxQ hxC
    have hxcl : x ∈ closure (Graph.face G segmentDrawing z) :=
      frontier_subset_closure (hfrontier.symm ▸ hxQ)
    exact hclosure hxcl ((p.mem_openRectangleCover_of_near_trace (by omega) hε hxC)
      (by simpa using hε.le))
  have hQinside : Q.carrier ⊆ inside p.trace := by
    intro x hx
    exact frontier_face_sdiff_curve_subset_inside hCsub (hp.isSeparating hn) hz
      ⟨hfrontier.symm ▸ hx, fun h ↦ Set.disjoint_left.mp hQoff hx h⟩
  refine ⟨m, Q, hinside ▸ Graph.mem_face hzext, hQinside, hinside ▸ hface,
    hinside ▸ hclosure, ?_⟩
  intro x hx
  have h := hQsub hx
  rw [hpoint] at h
  exact h.resolve_left fun hxC ↦ Set.disjoint_left.mp hQoff hx hxC

end InscribedPolygon
end Reeken.Geometry
