import Schoenflies.FaceCyclesLand

/-! # Simple polygon boundaries of finite polygonal cells

The finite graph must actually be drawn without crossings and be 2-connected.
Applying this theorem to the local square overlay and the inner-polygon arrangement
still requires constructing those graphs and verifying these hypotheses.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

/-- A bounded face of a finite 2-connected polygonal plane graph is the inside of an
actual finite simple polygon, and that polygon uses the original drawing. -/
theorem exists_polygon_of_bounded_face {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} [G.Finite] (hd : Graph.IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e))
    (hG : G.IsTwoConnected) {z : Plane} (hz : z ∈ Graph.exterior G drawing)
    (hb : Bornology.IsBounded (Graph.face G drawing z)) :
    ∃ m : ℕ, ∃ p : ClosedPolygon m,
      frontier (Graph.face G drawing z) = p.carrier ∧
      Graph.face G drawing z = inside p.carrier ∧ p.carrier ⊆ Graph.pointSet G drawing := by
  obtain ⟨e, u, v, D, hc⟩ := Graph.face_cycles' hd hpoly hG z hz
  obtain ⟨m, p, hp⟩ := exists_closedPolygon hc.isSeparating.isJordanCurve
    (hd.isPolygonal_edgesCover hpoly hc.isCycle.isWalk_cons (List.cons_ne_nil _ _))
  refine ⟨m, p, hc.frontier_eq.trans hp.symm, ?_, ?_⟩
  · rw [hp]
    exact hc.eq_inside_of_isBounded hb
  · rw [hp]
    apply Graph.edgesCover_subset_pointSet
    intro g hg
    exact hc.isCycle.isWalk_cons.edge_mem hg

end Reeken.Geometry
