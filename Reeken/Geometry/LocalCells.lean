import Reeken.Geometry.FiniteFaces
import Reeken.Geometry.SquareFaces
import Reeken.Geometry.SquareTwoConnected
import Reeken.Geometry.PolygonCells

/-! # The polygonal cell through a prescribed local boundary point

There are finitely many faces. Points of the chosen polygon side approaching the
boundary point therefore approach one fixed face inside the square. Its boundary
cycle gives the simple polygon used in Section 3.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

theorem exists_face_at_local_boundary [G.Finite] (hd : G.IsDrawing drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e)) (hG : G.IsTwoConnected)
    {C Ω : Set Plane} {c a : Plane} {r : ℝ}
    (he : Graph.pointSet G drawing = C ∪ squareBoundary c r)
    (hC : IsSeparating C) (hΩ : IsRegionOf C Ω)
    (haC : a ∈ C) (haS : a ∈ Plane.openSquare c r) :
    ∃ z ∈ Ω ∩ Plane.openSquare c r, a ∈ frontier (Graph.face G drawing z) := by
  let W := Ω ∩ Plane.openSquare c r
  have hWext : W ⊆ Graph.exterior G drawing := by
    rintro z ⟨hzΩ, hzS⟩ hz
    rw [he] at hz
    rcases hz with hzC | hzS'
    · exact hΩ.subset_compl hzΩ hzC
    · exact (show Plane.supDist z c < r from hzS).ne hzS'
  have hfaceW : ∀ z ∈ W, Graph.face G drawing z ⊆ W := by
    intro z hz x hx
    constructor
    · have hsub : Graph.exterior G drawing ⊆ Cᶜ := by
        rw [Graph.exterior, he]
        exact compl_subset_compl.mpr subset_union_left
      have hxC := connectedComponentIn_mono z hsub hx
      rwa [hΩ.connectedComponentIn_eq hC hz.1] at hxC
    · exact face_subset_openSquare (by rw [he]; exact subset_union_right) (hWext hz) hz.2 hx
  let F : Set (Set Plane) := (Graph.face G drawing) '' W
  have hF : F.Finite := (finite_faces hd hpoly hG).subset (by
    rintro s ⟨z, hz, rfl⟩
    exact ⟨z, hWext hz, rfl⟩)
  have hcover : ⋃₀ F = W := by
    apply Subset.antisymm
    · rintro x ⟨s, ⟨z, hz, rfl⟩, hx⟩
      exact hfaceW z hz hx
    · intro z hz
      exact ⟨Graph.face G drawing z, ⟨z, hz, rfl⟩, Graph.mem_face (hWext hz)⟩
  have haW : a ∈ closure W :=
    (Plane.isOpen_openSquare c r).closure_inter ⟨hΩ.subset_closure hC haC, haS⟩
  rw [← hcover, hF.closure_sUnion] at haW
  obtain ⟨s, ⟨z, hz, rfl⟩, has⟩ := mem_iUnion₂.mp haW
  refine ⟨z, hz, ?_⟩
  rw [(hd.isOpen_face z).frontier_eq]
  refine ⟨has, ?_⟩
  intro haf
  exact hΩ.subset_compl (hfaceW z hz haf).1 haC

theorem exists_clipped_cell [G.Finite] (hd : G.IsDrawing drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e)) (hG : G.IsTwoConnected)
    {C Ω : Set Plane} {c a : Plane} {r : ℝ}
    (he : Graph.pointSet G drawing = C ∪ squareBoundary c r)
    (hC : IsSeparating C) (hΩ : IsRegionOf C Ω)
    (haC : a ∈ C) (haS : a ∈ Plane.openSquare c r) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      a ∈ Q.carrier ∧ Q.carrier ⊆ C ∪ squareBoundary c r ∧
      Q.carrier \ C ⊆ Ω ∧ inside Q.carrier ⊆ Ω ∩ Plane.openSquare c r := by
  obtain ⟨z, hz, haF⟩ := exists_face_at_local_boundary hd hpoly hG he hC hΩ haC haS
  have hzext : z ∈ Graph.exterior G drawing := by
    intro hzg
    rw [he] at hzg
    rcases hzg with hzg | hzg
    · exact hΩ.subset_compl hz.1 hzg
    · exact (show Plane.supDist z c < r from hz.2).ne hzg
  have hS : squareBoundary c r ⊆ Graph.pointSet G drawing := by rw [he]; exact subset_union_right
  have hfaceΩ : Graph.face G drawing z ⊆ Ω := by
    have hsub : Graph.exterior G drawing ⊆ Cᶜ := by
      rw [Graph.exterior, he]
      exact compl_subset_compl.mpr subset_union_left
    have h := connectedComponentIn_mono z hsub
    rwa [hΩ.connectedComponentIn_eq hC hz.1] at h
  obtain ⟨m, Q, hfr, hface, hsub⟩ := exists_polygon_of_bounded_face hd hpoly hG hzext
    (isBounded_face_of_square hS hzext hz.2)
  refine ⟨m, Q, hfr ▸ haF, hsub.trans_eq he, ?_, ?_⟩
  · rw [← hfr, ← hΩ.frontier_eq hC]
    exact frontier_sdiff_frontier_subset hfaceΩ
  · rw [← hface]
    exact subset_inter hfaceΩ (face_subset_openSquare hS hzext hz.2)

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

/-- The actual simple polygon and local square supply the cell polygon on either side. -/
theorem Simple.exists_clipped_polygon (hp : p.Simple) (hn : 2 ≤ p.n)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) {c : Plane} {r : ℝ} (hr : 0 < r)
    (ha : p.vertex a ∈ Plane.openSquare c r)
    (hb : p.vertex b ∉ Plane.closedSquare c r) {Ω : Set Plane}
    (hΩ : IsRegionOf p.trace Ω) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      p.vertex a ∈ Q.carrier ∧ Q.carrier ⊆ p.trace ∪ squareBoundary c r ∧
      Q.carrier \ p.trace ⊆ Ω ∧ inside Q.carrier ⊆ Ω ∩ Plane.openSquare c r := by
  obtain ⟨points, hd, hG, he, _⟩ := hp.exists_twoConnected_square_overlay p hn hab hr ha hb
  apply exists_clipped_cell hd (fun e _ ↦ ?_) hG he (hp.isSeparating hn) hΩ
    (p.vertex_mem_trace a) ha
  rw [edgeArc_segmentDrawing]
  exact isPolygonal_segment _ _

end InscribedPolygon
end Reeken.Geometry
