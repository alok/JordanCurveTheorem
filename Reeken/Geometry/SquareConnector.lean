import Reeken.Geometry.ArcEndpoint
import Reeken.Geometry.ArcParametrization
import Reeken.Geometry.LocalCells
import Reeken.Geometry.BoundarySubpath

/-! # The square-boundary connector in the published Section 3 argument

The clipped cell meets both original arcs away from their common local vertex:
otherwise that vertex would be a free arc endpoint on a closed curve. A path around
the punctured cell then supplies the connector by first and last contact.
-/

open Set Schoenflies

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem Simple.exists_square_connector (hp : p.Simple) (hn : 2 ≤ p.n)
    {a b : Fin (p.n + 1)} (hab : a < b) {c : Plane} {r : ℝ} (hr : 0 < r)
    (ha : p.vertex a ∈ Plane.openSquare c r)
    (hb : p.vertex b ∉ Plane.closedSquare c r) {Ω : Set Plane}
    (hΩ : IsRegionOf p.trace Ω) :
    ∃ T : Set Plane, IsPreconnected T ∧ T ⊆ squareBoundary c r ∧
      (T ∩ p.forwardArc a b).Nonempty ∧ (T ∩ p.backwardArc a b).Nonempty ∧
      T \ p.trace ⊆ Ω := by
  obtain ⟨m, Q, haQ, hQcover, hQside, hQinside⟩ := hp.exists_clipped_polygon p hn hab.le hr ha hb hΩ
  have hS : IsClosed (squareBoundary c r) := by
    change IsClosed {z | Plane.supDist z c = r}
    rw [← Plane.frontier_closedSquare]
    exact isClosed_frontier
  have haS : p.vertex a ∉ squareBoundary c r := (show Plane.supDist (p.vertex a) c < r from ha).ne
  have hQclosed : Q.carrier ⊆ Plane.closedSquare c r := by
    rw [← Q.isSeparating_carrier.frontier_inside]
    apply frontier_subset_closure.trans
    apply closure_mono (fun z hz ↦ (hQinside hz).2) |>.trans
    apply (Plane.isClosed_closedSquare c r).closure_subset_iff.mpr
    intro z hz
    exact show Plane.supDist z c ≤ r from le_of_lt hz
  have hbQ : p.vertex b ∉ Q.carrier := fun h ↦ hb (hQclosed h)
  obtain ⟨hF, hB⟩ := hp.isArcBetween_cut_arcs p hn hab
  obtain ⟨x, hxQ, hxOther⟩ := Set.not_subset.mp
    (not_subset_arc_union_of_endpoint Q.isJordanCurve_carrier hB hS haQ haS)
  have hxF : x ∈ p.forwardArc a b := by
    have hx := hQcover hxQ
    rw [← p.arcs_union a b] at hx
    rcases hx with (hx | hx) | hx
    · exact hx
    · exact (hxOther (Or.inl hx)).elim
    · exact (hxOther (Or.inr hx)).elim
  have hxa : x ≠ p.vertex a := fun he ↦ hxOther (Or.inl (he ▸ hB.left_mem))
  obtain ⟨y, hyQ, hyOther⟩ := Set.not_subset.mp
    (not_subset_arc_union_of_endpoint Q.isJordanCurve_carrier hF hS haQ haS)
  have hyB : y ∈ p.backwardArc a b := by
    have hy := hQcover hyQ
    rw [← p.arcs_union a b] at hy
    rcases hy with (hy | hy) | hy
    · exact (hyOther (Or.inl hy)).elim
    · exact hy
    · exact (hyOther (Or.inr hy)).elim
  have hya : y ≠ p.vertex a := fun he ↦ hyOther (Or.inl (he ▸ hF.left_mem))
  obtain ⟨γ, hγ⟩ := (isPathConnected_punctured_jordan Q.isJordanCurve_carrier (p.vertex a)).joinedIn
    x ⟨hxQ, hxa⟩ y ⟨hyQ, hya⟩
  have hγI : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ Q.carrier \ {p.vertex a} := by
    intro t ht
    change γ.extend (↑(⟨t, ht⟩ : unitInterval)) ∈ _
    rw [γ.extend_extends']
    exact hγ ⟨t, ht⟩
  have hdis : Disjoint (γ.extend '' Icc 0 1) (p.forwardArc a b ∩ p.backwardArc a b) := by
    rw [hp.arcs_inter hab.le, Set.disjoint_left]
    rintro z ⟨t, ht, rfl⟩ (he | he)
    · exact (hγI t ht).2 he
    · exact hbQ (he ▸ (hγI t ht).1)
  have hcover : γ.extend '' Icc 0 1 ⊆ (p.forwardArc a b ∪ p.backwardArc a b) ∪ squareBoundary c r := by
    rw [p.arcs_union]
    rintro z ⟨t, ht, rfl⟩
    exact hQcover (hγI t ht).1
  obtain ⟨u, v, hu, huv, hv, huF, hvB, hSsub, _⟩ := exists_boundary_subpath γ.continuous_extend
    (p.isCompact_forwardArc a b).isClosed (p.isCompact_backwardArc a b).isClosed hS
    (by simpa using hxF) (by simpa using hyB) hdis hcover
  refine ⟨γ.extend '' Icc u v, isPreconnected_Icc.image _ γ.continuous_extend.continuousOn,
    hSsub, ⟨γ.extend u, ⟨u, ⟨le_rfl, huv.le⟩, rfl⟩, huF⟩,
    ⟨γ.extend v, ⟨v, ⟨huv.le, le_rfl⟩, rfl⟩, hvB⟩, ?_⟩
  rintro z ⟨⟨t, ht, rfl⟩, hnot⟩
  exact hQside ⟨(hγI t ⟨hu.trans ht.1, ht.2.trans hv⟩).1, hnot⟩

end Reeken.Geometry.InscribedPolygon
