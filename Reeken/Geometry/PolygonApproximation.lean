import Reeken.Geometry.InscribedPolygon

/-!
# Quantitative estimates for arbitrary inscribed polygons

The circular gap bound includes both omitted endpoint intervals. Thus every parameter
in the closed unit interval is within the maximum gap of a sampled parameter.
-/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E} (p : InscribedPolygon f)

theorem exists_near_parameter {t : ℝ} (ht : t ∈ Icc 0 1) :
    ∃ j : Fin (p.n + 1), dist t (p.time j) ≤ p.maxGap := by
  classical
  by_cases hfirst : p.time 0 ≤ t
  · let s := Finset.univ.filter fun j ↦ p.time j ≤ t
    have hs : s.Nonempty := ⟨0, by simp [s, hfirst]⟩
    obtain ⟨j, hj, hmax⟩ := s.exists_max_image p.time hs
    have hjt : p.time j ≤ t := (Finset.mem_filter.mp hj).2
    refine ⟨j, ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hjt)]
    by_cases hjlast : j = Fin.last p.n
    · subst j
      have hg := p.gap_le_maxGap (Fin.last p.n)
      rw [gap_last] at hg
      linarith [ht.2, (p.time_mem 0).1]
    · obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hjlast
      have ht_next : t < p.time k.succ := by
        by_contra! h
        have hm := hmax k.succ (by simp [s, h])
        rw [← hk] at hm
        exact (not_le_of_gt (p.increasing (by simp))) hm
      have hg := p.gap_le_maxGap k.castSucc
      rw [gap_castSucc, hk] at hg
      linarith
  · refine ⟨0, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hfirst))]
    have hg := p.gap_le_maxGap (Fin.last p.n)
    rw [gap_last] at hg
    linarith [ht.1, (p.time_mem (Fin.last p.n)).2]

variable [NormedSpace ℝ E]

theorem trace_near_curve {ε : ℝ} (hε : p.maxEdge < ε) :
    ∀ x ∈ p.trace, ∃ y ∈ f '' Icc 0 1, dist x y < ε := by
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  refine ⟨p.vertex j, ⟨p.time j, Ico_subset_Icc_self (p.time_mem j), rfl⟩, ?_⟩
  rw [dist_comm]
  exact (dist_left_le_of_mem_segment hj).trans_lt ((p.edgeLength_le_maxEdge j).trans_lt hε)

theorem curve_near_trace {ε δ : ℝ}
    (hd : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      dist a b < δ → dist (f a) (f b) < ε) (hgap : p.maxGap < δ) :
    ∀ y ∈ f '' Icc 0 1, ∃ x ∈ p.trace, dist x y < ε := by
  rintro y ⟨t, ht, rfl⟩
  obtain ⟨j, hj⟩ := p.exists_near_parameter ht
  refine ⟨p.vertex j, mem_iUnion.mpr ⟨j, left_mem_segment ℝ _ _⟩, ?_⟩
  apply hd _ (Ico_subset_Icc_self (p.time_mem j)) _ ht
  rw [dist_comm]
  exact hj.trans_lt hgap

end Reeken.Geometry.InscribedPolygon
