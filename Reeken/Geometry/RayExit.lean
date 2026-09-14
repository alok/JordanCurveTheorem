import Reeken.Geometry.ExposedVertex

/-! # The first exit of an inward polygon ray

A ray which starts inside the polygon reaches its first boundary point in finite
time. Before that point it stays inside. The endpoint is obtained by minimizing
the parameter on a compact set of boundary intersections.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem image_Icc_subset_inside_of_avoids {C : Set Plane} (hC : IsSeparating C)
    {f : ℝ → Plane} (hf : Continuous f) {s t : ℝ} (hst : s ≤ t)
    (hs : f s ∈ inside C) (havoid : ∀ r ∈ Icc s t, f r ∉ C) :
    ∀ r ∈ Icc s t, f r ∈ inside C := by
  have hconn : IsPreconnected (f '' Icc s t) :=
    (convex_Icc s t).isPreconnected.image f hf.continuousOn
  have hsub : f '' Icc s t ⊆ inside C := by
    apply hconn.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
    · rw [inside_union_outside]
      rintro x ⟨r, hr, rfl⟩
      exact havoid r hr
    · exact ⟨f s, mem_image_of_mem f (left_mem_Icc.mpr hst), hs⟩
  exact fun r hr ↦ hsub (mem_image_of_mem f hr)

theorem exists_first_ray_exit_of_ne {C : Set Plane} (hC : IsSeparating C) {a v : Plane}
    (hv : v ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hin : ∀ ε : ℝ, 0 < ε → ε < δ → a + ε • v ∈ inside C) :
    ∃ t : ℝ, 0 < t ∧ a + t • v ∈ C ∧
      ∀ s : ℝ, 0 < s → s < t → a + s • v ∈ inside C := by
  let ε₀ := δ / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀δ : ε₀ < δ := by dsimp [ε₀]; linarith
  have hstart := hin ε₀ hε₀ hε₀δ
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨B, hB, hbound⟩ := hC.isBounded_inside.exists_pos_norm_le
  let R := ε₀ + (B + ‖a‖ + 1) / ‖v‖
  have hRε : ε₀ < R := by dsimp [R]; exact lt_add_of_pos_right _ (by positivity)
  have hR : 0 < R := hε₀.trans hRε
  have hRmul : B + ‖a‖ < R * ‖v‖ := by
    have he : R * ‖v‖ = ε₀ * ‖v‖ + (B + ‖a‖ + 1) := by
      dsimp [R]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hvnorm)]
    rw [he]
    nlinarith [mul_pos hε₀ hvnorm]
  have hfar : a + R • v ∉ inside C := by
    intro hfar
    have hnorm := norm_sub_le (a + R • v) a
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at hnorm
    linarith [hbound (a + R • v) hfar]
  let f : ℝ → Plane := fun t ↦ a + t • v
  have hf : Continuous f := by dsimp [f]; fun_prop
  let S := Icc ε₀ R ∩ f ⁻¹' C
  have hSne : S.Nonempty := by
    by_contra hne
    have havoid : ∀ r ∈ Icc ε₀ R, f r ∉ C := by
      intro r hr hrc
      exact hne ⟨r, hr, hrc⟩
    exact hfar (image_Icc_subset_inside_of_avoids hC hf hRε.le hstart havoid R (right_mem_Icc.mpr hRε.le))
  have hScompact : IsCompact S := isCompact_Icc.inter_right (hC.isClosed.preimage hf)
  obtain ⟨t, htS, hmin⟩ := hScompact.exists_isMinOn hSne continuous_id.continuousOn
  have ht : 0 < t := hε₀.trans_le htS.1.1
  refine ⟨t, ht, htS.2, ?_⟩
  intro s hs hst
  by_cases hsε : s < ε₀
  · exact hin s hs (hsε.trans hε₀δ)
  · have hεs : ε₀ ≤ s := le_of_not_gt hsε
    have havoid : ∀ r ∈ Icc ε₀ s, f r ∉ C := by
      intro r hr hrC
      have hrt : r < t := hr.2.trans_lt hst
      have hrS : r ∈ S := ⟨⟨hr.1, hrt.le.trans htS.1.2⟩, hrC⟩
      exact hrt.not_ge (hmin hrS)
    exact image_Icc_subset_inside_of_avoids hC hf hεs hstart havoid s (right_mem_Icc.mpr hεs)

theorem exists_first_ray_exit {C : Set Plane} (hC : IsSeparating C) {a v : Plane}
    (ha : a ∈ C) {δ : ℝ} (hδ : 0 < δ)
    (hin : ∀ ε : ℝ, 0 < ε → ε < δ → a + ε • v ∈ inside C) :
    ∃ t : ℝ, 0 < t ∧ a + t • v ∈ C ∧
      ∀ s : ℝ, 0 < s → s < t → a + s • v ∈ inside C := by
  have hv : v ≠ 0 := by
    intro hv
    have hstart := hin (δ / 2) (by linarith) (by linarith)
    simp only [hv, smul_zero, add_zero] at hstart
    exact hstart.1 ha
  exact exists_first_ray_exit_of_ne hC hv hδ hin

/-- A point outside the inside gives an upper bound for the first-hit parameter. -/
theorem exists_first_ray_exit_le {C : Set Plane} (hC : IsSeparating C) {a v : Plane}
    (hv : v ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hin : ∀ ε : ℝ, 0 < ε → ε < δ → a + ε • v ∈ inside C)
    {R : ℝ} (hR : 0 < R) (hout : a + R • v ∉ inside C) :
    ∃ t : ℝ, 0 < t ∧ t ≤ R ∧ a + t • v ∈ C ∧
      ∀ s : ℝ, 0 < s → s < t → a + s • v ∈ inside C := by
  obtain ⟨t, ht, htc, hseg⟩ := exists_first_ray_exit_of_ne hC hv hδ hin
  exact ⟨t, ht, le_of_not_gt (fun hRt ↦ hout (hseg R hR hRt)), htc, hseg⟩

/-- A segment from an interior point to a point outside the closed inside has a
first boundary crossing strictly between its endpoints. -/
theorem exists_boundary_hit_openSegment {C : Set Plane} (hC : IsSeparating C)
    {a b : Plane} (ha : a ∈ inside C) (hb : b ∉ closure (inside C)) :
    ∃ x ∈ C, x ∈ openSegment ℝ a b ∧ openSegment ℝ a x ⊆ inside C := by
  have hab : b ≠ a := fun he ↦ hb (he ▸ subset_closure ha)
  have hv : b - a ≠ 0 := sub_ne_zero.mpr hab
  let f : ℝ → Plane := fun t ↦ a + t • (b - a)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hzero : (0 : ℝ) ∈ f ⁻¹' inside C := by simpa [f] using ha
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hC.isOpen_inside.preimage hf) 0 hzero
  have hin : ∀ ε : ℝ, 0 < ε → ε < δ → a + ε • (b - a) ∈ inside C := by
    intro ε hε hεδ
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using hεδ
  have hout : a + (1 : ℝ) • (b - a) ∉ inside C := by
    simpa using (fun hbin ↦ hb (subset_closure hbin) : b ∉ inside C)
  obtain ⟨t, ht, ht1, htc, hseg⟩ := exists_first_ray_exit_le hC hv hδ hin zero_lt_one hout
  have htlt : t < 1 := lt_of_le_of_ne ht1 (by
    intro he
    have hbc : b ∈ C := by simpa [he] using htc
    exact hb (frontier_subset_closure (hC.frontier_inside.symm ▸ hbc)))
  refine ⟨a + t • (b - a), htc, ?_, ?_⟩
  · refine ⟨1 - t, t, by linarith, ht, by ring, ?_⟩
    module
  · rintro x ⟨u, v, hu, hv', huv, rfl⟩
    have hvt : v * t < t := by nlinarith
    have hx := hseg (v * t) (mul_pos hv' ht) hvt
    convert hx using 1
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul, huv, one_smul]

/-- A segment crossing an inside from endpoints outside the closed inside meets
the boundary no higher than any chosen interior point, for any linear height.
For a triangle this forces a crossing on one of the sides away from the base. -/
theorem exists_boundary_hit_below {C : Set Plane} (hC : IsSeparating C)
    (F : Plane →L[ℝ] ℝ) {p q z : Plane}
    (hp : F p ≤ F z → p ∉ closure (inside C))
    (hq : F q ≤ F z → q ∉ closure (inside C))
    (hz : z ∈ inside C) (hzseg : z ∈ segment ℝ p q) :
    ∃ x ∈ C, x ∈ segment ℝ p q ∧ F x ≤ F z := by
  have hend : F p ≤ F z ∨ F q ≤ F z := by
    apply min_le_iff.mp
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hzseg
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      min (F p) (F q) = u * min (F p) (F q) + v * min (F p) (F q) := by
        rw [← add_mul, huv, one_mul]
      _ ≤ u * F p + v * F q := by gcongr <;> simp
  have hhit : ∀ r ∈ segment ℝ p q, r ∉ closure (inside C) → F r ≤ F z →
      ∃ x ∈ C, x ∈ segment ℝ p q ∧ F x ≤ F z := by
    intro r hr hrout hFr
    obtain ⟨x, hxC, hxzr, _⟩ := exists_boundary_hit_openSegment hC hz hrout
    refine ⟨x, hxC, (convex_segment p q).segment_subset hzseg hr
      (openSegment_subset_segment ℝ z r hxzr), ?_⟩
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hxzr
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      u * F z + v * F r ≤ u * F z + v * F z := by gcongr
      _ = F z := by rw [← add_mul, huv, one_mul]
  exact hend.elim (fun hFp ↦ hhit p (left_mem_segment ℝ p q) (hp hFp) hFp)
    (fun hFq ↦ hhit q (right_mem_segment ℝ p q) (hq hFq) hFq)

/-- Every polygon has an inward straight cut from a vertex to its next boundary
intersection. The cut's open part lies in the polygon's inside. -/
theorem exists_vertex_first_ray_exit {m : ℕ} (P : ClosedPolygon m) :
    ∃ (i : ZMod (m + 3)) (t : ℝ), 0 < t ∧
      P.vertex i + t • (P.tang i + P.rayIn i) ∈ P.carrier ∧
      ∀ s : ℝ, 0 < s → s < t →
        P.vertex i + s • (P.tang i + P.rayIn i) ∈ inside P.carrier := by
  obtain ⟨i, δ, hδ, hin⟩ := exists_vertex_inward_bisector P
  obtain ⟨t, ht, htc, hseg⟩ := exists_first_ray_exit P.isSeparating_carrier
    (ClosedPolygon.vertex_mem_carrier (P := P) (i := i)) hδ hin
  exact ⟨i, t, ht, htc, hseg⟩

/-- The first hit is on a nonincident edge, and the entire open straight cut lies
inside. Its far endpoint may be in the interior of that edge. -/
theorem exists_vertex_to_nonincident_edge_cut {m : ℕ} (P : ClosedPolygon m) :
    ∃ (i j : ZMod (m + 3)) (q : Plane),
      j ≠ i ∧ j ≠ i - 1 ∧ q ∈ P.edge j ∧ P.vertex i ≠ q ∧
      openSegment ℝ (P.vertex i) q ⊆ inside P.carrier := by
  obtain ⟨i, t, ht, htc, hseg⟩ := exists_vertex_first_ray_exit P
  let d := P.tang i + P.rayIn i
  let q := P.vertex i + t • d
  have hd : d ≠ 0 := by
    intro hd
    have hnear := hseg (t / 2) (by linarith) (by linarith)
    change P.vertex i + (t / 2) • d ∈ inside P.carrier at hnear
    rw [hd, smul_zero, add_zero] at hnear
    exact hnear.1 (ClosedPolygon.vertex_mem_carrier (P := P) (i := i))
  have hneq : P.vertex i ≠ q := by
    intro he
    have hz : t • d = 0 := by
      change P.vertex i = P.vertex i + t • d at he
      exact add_eq_left.mp he.symm
    exact (smul_eq_zero.mp hz).elim (ne_of_gt ht) hd
  have hnotnext : q ∉ P.edge i := by
    intro hq
    obtain ⟨r, _, hr⟩ := ClosedPolygon.mem_edge_sub hq
    have he : t • (P.tang i + P.rayIn i) = r • P.tang i := by simpa [q, d] using hr
    have hdet := congrArg (Plane.det (P.tang i)) he
    simp only [Plane.det_smul_right, Plane.det_add_right, Plane.det_self, zero_add, mul_zero] at hdet
    have hne : Plane.det (P.tang i) (P.rayIn i) ≠ 0 := by
      rw [Plane.det_comm]
      exact neg_ne_zero.mpr (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))
    exact (mul_ne_zero (ne_of_gt ht) hne) hdet
  have hnotprev : q ∉ P.edge (i - 1) := by
    intro hq
    obtain ⟨r, _, hr⟩ := ClosedPolygon.mem_edge_pred_sub hq
    have he : t • (P.tang i + P.rayIn i) = r • P.rayIn i := by simpa [q, d] using hr
    have hdet := congrArg (Plane.det (P.rayIn i)) he
    simp only [Plane.det_smul_right, Plane.det_add_right, Plane.det_self, add_zero, mul_zero] at hdet
    exact (mul_ne_zero (ne_of_gt ht) (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))) hdet
  obtain ⟨j, hj⟩ := mem_iUnion.mp htc
  refine ⟨i, j, q, fun he ↦ hnotnext (he ▸ hj), fun he ↦ hnotprev (he ▸ hj), hj, hneq, ?_⟩
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  have hv1 : v < 1 := by linarith
  have hvt : v * t < t := by nlinarith
  have hx := hseg (v * t) (mul_pos hv ht) hvt
  convert hx using 1
  dsimp [q, d]
  rw [smul_add, smul_smul, ← add_assoc, ← add_smul, huv, one_smul]

end Reeken.Geometry
