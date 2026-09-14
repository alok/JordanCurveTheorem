import Reeken.Geometry.PolygonDiagonal

/-! # Internal diagonals with redundant vertices allowed

Normalization supplies a diagonal unless the carrier is a triangle. In that case
an extra vertex lies in the open part of one edge and joins the opposite corner
through the triangular inside.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem nonadjacent_of_openSegment_inside {m : ℕ} (P : PrePolygon m)
    {i j : ZMod (m + 3)} (hseg : openSegment ℝ (P.vertex i) (P.vertex j) ⊆ inside P.carrier) :
    j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 := by
  have hx : (1 / 2 : ℝ) • P.vertex i + (1 / 2 : ℝ) • P.vertex j ∈
      openSegment ℝ (P.vertex i) (P.vertex j) := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxin := (hseg hx).1
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hxcar : (1 / 2 : ℝ) • P.vertex i + (1 / 2 : ℝ) • P.vertex j ∈ P.carrier := by
      rw [he] at hx ⊢
      rw [openSegment_same, mem_singleton_iff] at hx
      rw [hx]
      exact P.vertex_mem_carrier i
    exact hxin hxcar
  · intro he
    apply hxin
    apply PrePolygon.edge_subset_carrier i
    exact openSegment_subset_segment ℝ _ _ (he ▸ hx)
  · intro he
    apply hxin
    apply PrePolygon.edge_subset_carrier (i - 1)
    change _ ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
    rw [sub_add_cancel, segment_symm]
    exact openSegment_subset_segment ℝ _ _ (he ▸ hx)

theorem openSegment_triangle_zero_edge_inside (T : ClosedPolygon 0) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.vertex 1) (T.vertex 2)) :
    openSegment ℝ (T.vertex 0) x ⊆ inside T.carrier := by
  have hdet : Plane.det (T.vertex 1 - T.vertex 0) (T.vertex 2 - T.vertex 0) ≠ 0 := by
    have h := T.corner 0
    change Plane.det (T.vertex (-1) - T.vertex 0) (T.vertex 1 - T.vertex 0) ≠ 0 at h
    rw [show (-1 : ZMod 3) = 2 by decide, Plane.det_comm] at h
    exact neg_ne_zero.mp h
  have hr : range T.vertex = {T.vertex 0, T.vertex 1, T.vertex 2} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases hi i with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl) <;> exact mem_range_self _
  rw [inside_triangle_eq_interior_hull, hr]
  exact openSegment_apex_base_subset_interior hdet hx

theorem exists_triangle_vertex_segment_inside (T : ClosedPolygon 0) {x : Plane}
    (hx : x ∈ T.carrier) (hxv : x ∉ range T.vertex) :
    ∃ i, openSegment ℝ (T.vertex i) x ⊆ inside T.carrier := by
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
  have hxopen : x ∈ openSegment ℝ (T.vertex k) (T.vertex (k + 1)) :=
    mem_openSegment_of_ne_left_right
      (fun he ↦ hxv ⟨k, he⟩) (fun he ↦ hxv ⟨k + 1, he⟩) hxk
  let R := T.rotate (k - 1)
  have hR : R.carrier = T.carrier := PrePolygon.carrier_rotate T.toPre (k - 1)
  have hxR : x ∈ openSegment ℝ (R.vertex 1) (R.vertex 2) := by
    change x ∈ openSegment ℝ (T.vertex (k - 1 + 1)) (T.vertex (k - 1 + 2))
    rw [sub_add_cancel, show k - 1 + 2 = k + 1 by ring]
    exact hxopen
  have hsub := openSegment_triangle_zero_edge_inside R hxR
  rw [hR] at hsub
  refine ⟨k - 1, ?_⟩
  simpa only [R, ClosedPolygon.rotate_vertex, add_zero] using hsub

theorem exists_internal_diagonal_prePolygon {m : ℕ} (P : PrePolygon m) (hm : 0 < m) :
    ∃ (i j : ZMod (m + 3)), j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      openSegment ℝ (P.vertex i) (P.vertex j) ⊆ inside P.carrier := by
  classical
  obtain ⟨n, Q, hn, hQ, hv⟩ := exists_closedPolygon_le_of_prePolygon m P
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have hex : ∃ j, P.vertex j ∉ range Q.vertex := by
      by_contra hh
      push Not at hh
      choose f hf using hh
      have hfinj : Function.Injective f := by
        intro a b hab
        apply P.vertex_inj
        exact (hf a).symm.trans ((congrArg Q.vertex hab).trans (hf b))
      have hcard := Fintype.card_le_of_injective f hfinj
      simp only [ZMod.card] at hcard
      omega
    obtain ⟨j, hj⟩ := hex
    have hxQ : P.vertex j ∈ Q.carrier := hQ.symm ▸ P.vertex_mem_carrier j
    obtain ⟨k, hk⟩ := exists_triangle_vertex_segment_inside Q hxQ hj
    obtain ⟨i, hi⟩ := hv (mem_range_self k)
    rw [hQ, ← hi] at hk
    exact ⟨i, j, (nonadjacent_of_openSegment_inside P hk).1,
      (nonadjacent_of_openSegment_inside P hk).2.1,
      (nonadjacent_of_openSegment_inside P hk).2.2, hk⟩
  · obtain ⟨a, b, -, -, -, hab⟩ := exists_internal_diagonal Q hnpos
    obtain ⟨i, hi⟩ := hv (mem_range_self a)
    obtain ⟨j, hj⟩ := hv (mem_range_self b)
    rw [hQ, ← hi, ← hj] at hab
    exact ⟨i, j, (nonadjacent_of_openSegment_inside P hab).1,
      (nonadjacent_of_openSegment_inside P hab).2.1,
      (nonadjacent_of_openSegment_inside P hab).2.2, hab⟩

end Reeken.Geometry
