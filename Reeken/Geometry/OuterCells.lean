import Reeken.Geometry.RectangleCells
import Reeken.Geometry.ExteriorBounds

/-! # The outer cell of the finite rectangle arrangement

The unbounded face gives the exterior analogue of the inner polygon: its closed
outside avoids every open covering rectangle, and its boundary belongs to the
rectangle cover on the original polygon's outside.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem exists_polygon_of_unbounded_face {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} [G.Finite] (hd : Graph.IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e))
    (hG : G.IsTwoConnected) {z : Plane} (hz : z ∈ Graph.exterior G drawing)
    (hb : ¬ Bornology.IsBounded (Graph.face G drawing z)) :
    ∃ m : ℕ, ∃ p : ClosedPolygon m,
      frontier (Graph.face G drawing z) = p.carrier ∧
      Graph.face G drawing z = outside p.carrier ∧ p.carrier ⊆ Graph.pointSet G drawing := by
  obtain ⟨e, u, v, D, hc⟩ := Graph.face_cycles' hd hpoly hG z hz
  obtain ⟨m, p, hp⟩ := exists_closedPolygon hc.isSeparating.isJordanCurve
    (hd.isPolygonal_edgesCover hpoly hc.isCycle.isWalk_cons (List.cons_ne_nil _ _))
  refine ⟨m, p, hc.frontier_eq.trans hp.symm, ?_, ?_⟩
  · rw [hp]
    exact hc.eq_inside_or_outside.resolve_left fun h ↦ hb (h ▸ hc.isSeparating.isBounded_inside)
  · rw [hp]
    apply Graph.edgesCover_subset_pointSet
    intro g hg
    exact hc.isCycle.isWalk_cons.edge_mem hg

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem Simple.exists_rectangle_outer_cell (hp : p.Simple) (hn : 2 ≤ p.n)
    {ε : ℝ} (hε : 0 < ε) {a b : Fin (p.n + 1)}
    (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b)) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      Q.carrier ⊆ outside p.trace ∧ outside Q.carrier ⊆ outside p.trace ∧
      closure (outside Q.carrier) ⊆ (p.openRectangleCover ε)ᶜ ∧
      Q.carrier ⊆ p.rectangleCover ε := by
  obtain ⟨q, points, _, hd, htwo, hpoint, _⟩ := hp.exists_rectangle_overlay p hn hε hfar
  let G := overlayGraph (p.pieces ++ polygonFamilyPieces q) points
  have htrace : p.trace ⊆ p.openRectangleCover ε := by
    intro x hx
    exact p.mem_openRectangleCover_of_near_trace (by omega) hε hx (by simpa using hε.le)
  have hdraw : Graph.pointSet G segmentDrawing ⊆ p.rectangleCover ε := by
    rw [hpoint]
    rintro x (hx | hx)
    · exact p.openRectangleCover_subset ε (htrace hx)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j, (isClosed_closedEdgeRectangle _ _ _ _).frontier_subset hj⟩
  obtain ⟨r, hr, hR⟩ := Plane.exists_closedSquare_of_isBounded
    (p.isCompact_rectangleCover (by omega) ε).isBounded
  let z := Plane.mk (r + 1) 0
  have hzfar : z ∈ Plane.beyondSquare r := by
    left
    change r < |r + 1|
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hzext : z ∈ Graph.exterior G segmentDrawing :=
    Graph.beyondSquare_subset_exterior (hdraw.trans hR) hzfar
  have hzu : ¬ Bornology.IsBounded (Graph.face G segmentDrawing z) := by
    intro hb
    exact Graph.not_isBounded_beyondSquare r
      (hb.subset (Graph.beyondSquare_subset_face (hdraw.trans hR) hzfar))
  have hzR : z ∉ p.rectangleCover ε := by
    intro h
    exact (Plane.beyondSquare_eq_compl r ▸ hzfar) (hR h)
  have hzC : z ∈ outside p.trace := beyondSquare_subset_outside
    ((htrace.trans (p.openRectangleCover_subset ε)).trans hR) hzfar
  have hCsub : p.trace ⊆ Graph.pointSet G segmentDrawing := by
    rw [hpoint]
    exact subset_union_left
  have hface : Graph.face G segmentDrawing z ⊆ outside p.trace := face_subset_outside hCsub hzC
  have hclosure : closure (Graph.face G segmentDrawing z) ⊆ (p.openRectangleCover ε)ᶜ := by
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    have hboundary : frontier (p.closedRectangle ε j) ⊆ Graph.pointSet G segmentDrawing := by
      rw [hpoint]
      exact fun y hy ↦ Or.inr (mem_iUnion.mpr ⟨j, hy⟩)
    exact closure_face_subset_compl_interior (isClosed_closedEdgeRectangle _ _ _ _)
      hboundary hzext (fun h ↦ hzR (mem_iUnion.mpr ⟨j, h⟩)) hx
      (p.openRectangle_subset_interior ε j hj)
  obtain ⟨m, Q, hfrontier, houtside, hQsub⟩ := exists_polygon_of_unbounded_face hd
    (fun e _ ↦ by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _) htwo hzext hzu
  have hQoff : Disjoint Q.carrier p.trace := by
    rw [Set.disjoint_left]
    intro x hxQ hxC
    exact hclosure (frontier_subset_closure (hfrontier.symm ▸ hxQ)) (htrace hxC)
  refine ⟨m, Q, ?_, houtside ▸ hface, houtside ▸ hclosure, hQsub.trans hdraw⟩
  intro x hx
  exact frontier_face_sdiff_curve_subset_outside hCsub (hp.isSeparating hn) hzC
    ⟨hfrontier.symm ▸ hx, fun h ↦ Set.disjoint_left.mp hQoff hx h⟩

end InscribedPolygon
end Reeken.Geometry
