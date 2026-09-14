import Reeken.Nonstandard.Metric
import Reeken.Geometry.SimpleLoop

/-!
# Inverse infinitesimal continuity on a simple loop

The endpoint alternatives are essential: inverse continuity for `[0,1]` without them
would be false. This is the compactness step behind Kanovei–Reeken Lemma 1.
-/

open Filter Set

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [MetricSpace E]

/-- Close curve points have close parameters, possibly across the identified endpoints. -/
theorem near_parameters_or_endpoints (f : Reeken.Geometry.SimpleLoop E) {x y : Star U ℝ}
    (hx : x ∈ starSet (Icc 0 1)) (hy : y ∈ starSet (Icc 0 1))
    (hxy : Near (map f x) (map f y)) :
    Near x y ∨ (Near x (std 0) ∧ Near y (std 1)) ∨
      (Near x (std 1) ∧ Near y (std 0)) := by
  obtain ⟨a, ha, hxa⟩ := compact_standard_part isCompact_Icc hx
  obtain ⟨b, hb, hyb⟩ := compact_standard_part isCompact_Icc hy
  have hfa := hxa.map_compact isCompact_Icc f.continuousOn hx ((std_mem_starSet _ _).mpr ha)
  have hfb := hyb.map_compact isCompact_Icc f.continuousOn hy ((std_mem_starSet _ _).mpr hb)
  have hab : f a = f b := by
    simpa only [map_std, near_std_std] using hfa.symm.trans (hxy.trans hfb)
  rcases f.eq_or_endpoints ha hb hab with hab | ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
  · subst b
    exact Or.inl (hxa.trans hyb.symm)
  · subst a
    subst b
    exact Or.inr (Or.inl ⟨hxa, hyb⟩)
  · subst a
    subst b
    exact Or.inr (Or.inr ⟨hxa, hyb⟩)

/-- The half-circle bound rules out the endpoint alternatives for an increasing gap. -/
theorem small_forward_gap (f : Reeken.Geometry.SimpleLoop E) (x y : ι → ℝ)
    (hx : ∀ᶠ i in U, x i ∈ Icc 0 1) (hy : ∀ᶠ i in U, y i ∈ Icc 0 1)
    (hgap : ∀ᶠ i in U, x i ≤ y i ∧ y i - x i ≤ 1 / 2)
    (hxy : Near (ofSeq (U := U) (fun i ↦ f (x i))) (ofSeq (fun i ↦ f (y i)))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, y i - x i < ε := by
  have hn := near_parameters_or_endpoints f (x := ofSeq x) (y := ofSeq y) hx hy hxy
  rcases hn with hn | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · intro ε hε
    filter_upwards [hn ε hε] with i hi
    change dist (x i) (y i) < ε at hi
    rw [Real.dist_eq, abs_sub_comm] at hi
    exact (le_abs_self _).trans_lt hi
  · have hfalse : ∀ᶠ i in (U : Filter ι), False := by
      filter_upwards [hgap, h0 (1 / 8) (by norm_num), h1 (1 / 8) (by norm_num)]
        with i hi hxi hyi
      change dist (x i) 0 < 1 / 8 at hxi
      change dist (y i) 1 < 1 / 8 at hyi
      rw [Real.dist_eq] at hxi hyi
      have hxi' := (abs_lt.mp hxi).2
      have hyi' := (abs_lt.mp hyi).1
      linarith [hi.2]
    obtain ⟨_, h⟩ := hfalse.exists
    exact h.elim
  · have hfalse : ∀ᶠ i in (U : Filter ι), False := by
      filter_upwards [hgap, h1 (1 / 8) (by norm_num), h0 (1 / 8) (by norm_num)]
        with i hi hxi hyi
      change dist (x i) 1 < 1 / 8 at hxi
      change dist (y i) 0 < 1 / 8 at hyi
      rw [Real.dist_eq] at hxi hyi
      have hxi' := (abs_lt.mp hxi).1
      have hyi' := (abs_lt.mp hyi).2
      linarith [hi.1]
    obtain ⟨_, h⟩ := hfalse.exists
    exact h.elim

/-- The closing edge also has an infinitesimal parameter gap when the retained
parameter interval spans at least half the circle. -/
theorem small_wrap_gap (f : Reeken.Geometry.SimpleLoop E) (x y : ι → ℝ)
    (hx : ∀ᶠ i in U, x i ∈ Icc 0 1) (hy : ∀ᶠ i in U, y i ∈ Icc 0 1)
    (hspan : ∀ᶠ i in U, 1 / 2 ≤ y i - x i)
    (hxy : Near (ofSeq (U := U) (fun i ↦ f (x i))) (ofSeq (fun i ↦ f (y i)))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, 1 - y i + x i < ε := by
  have hn := near_parameters_or_endpoints f (x := ofSeq x) (y := ofSeq y) hx hy hxy
  rcases hn with hn | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have hfalse : ∀ᶠ i in (U : Filter ι), False := by
      filter_upwards [hspan, hn (1 / 4) (by norm_num)] with i hi hdi
      change dist (x i) (y i) < 1 / 4 at hdi
      rw [Real.dist_eq] at hdi
      have h := (abs_lt.mp hdi).1
      linarith
    obtain ⟨_, h⟩ := hfalse.exists
    exact h.elim
  · intro ε hε
    filter_upwards [h0 (ε / 2) (half_pos hε), h1 (ε / 2) (half_pos hε)] with i hxi hyi
    change dist (x i) 0 < ε / 2 at hxi
    change dist (y i) 1 < ε / 2 at hyi
    rw [Real.dist_eq] at hxi hyi
    have hxi' := (abs_lt.mp hxi).2
    have hyi' := (abs_lt.mp hyi).1
    linarith
  · have hfalse : ∀ᶠ i in (U : Filter ι), False := by
      filter_upwards [hspan, h1 (1 / 8) (by norm_num), h0 (1 / 8) (by norm_num)]
        with i hi hxi hyi
      change dist (x i) 1 < 1 / 8 at hxi
      change dist (y i) 0 < 1 / 8 at hyi
      rw [Real.dist_eq] at hxi hyi
      have hxi' := (abs_lt.mp hxi).1
      have hyi' := (abs_lt.mp hyi).2
      linarith
    obtain ⟨_, h⟩ := hfalse.exists
    exact h.elim

end Reeken.NSA
