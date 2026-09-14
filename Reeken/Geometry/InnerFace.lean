import Reeken.Geometry.RectangleCells

/-! # Inner faces of drawings containing a closed cover of a polygon

This form of the cell construction allows extra drawn segments. It retains the
identity of the polygon interior with its drawing face, so every extra drawn
segment is known to avoid that interior.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem exists_inner_face_polygon {β ι : Type*} {G : Graph Plane β} [G.Finite]
    {drawing : β → ℝ → Plane} (hd : Graph.IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e)) (htwo : G.IsTwoConnected)
    {C : Set Plane} (hC : IsSeparating C) (hCsub : C ⊆ Graph.pointSet G drawing)
    {D O : ι → Set Plane} (hD : ∀ j, IsClosed (D j))
    (hboundary : ∀ j, frontier (D j) ⊆ Graph.pointSet G drawing)
    (hO : ∀ j, O j ⊆ interior (D j)) (hcover : C ⊆ ⋃ j, O j)
    {z : Plane} (hz : z ∈ inside C) (hzext : z ∈ Graph.exterior G drawing)
    (hzD : ∀ j, z ∉ D j) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      z ∈ inside Q.carrier ∧ Q.carrier ⊆ inside C ∧ inside Q.carrier ⊆ inside C ∧
      closure (inside Q.carrier) ⊆ (⋃ j, O j)ᶜ ∧
      Q.carrier ⊆ Graph.pointSet G drawing ∧
      inside Q.carrier = Graph.face G drawing z := by
  have hface : Graph.face G drawing z ⊆ inside C := face_subset_inside hCsub hz
  have hclosure : closure (Graph.face G drawing z) ⊆ (⋃ j, O j)ᶜ := by
    intro x hx hxO
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxO
    exact closure_face_subset_compl_interior (hD j) (hboundary j) hzext (hzD j) hx (hO j hj)
  obtain ⟨m, Q, hfrontier, hinside, hQsub⟩ := exists_polygon_of_bounded_face hd hpoly htwo
    hzext (hC.isBounded_inside.subset hface)
  have hQoff : Disjoint Q.carrier C := by
    rw [Set.disjoint_left]
    intro x hxQ hxC
    exact hclosure (frontier_subset_closure (hfrontier.symm ▸ hxQ)) (hcover hxC)
  have hQinside : Q.carrier ⊆ inside C := by
    intro x hx
    exact frontier_face_sdiff_curve_subset_inside hCsub hC hz
      ⟨hfrontier.symm ▸ hx, fun h ↦ Set.disjoint_left.mp hQoff hx h⟩
  exact ⟨m, Q, hinside ▸ Graph.mem_face hzext, hQinside, hinside ▸ hface,
    hinside ▸ hclosure, hQsub, hinside.symm⟩

end Reeken.Geometry
