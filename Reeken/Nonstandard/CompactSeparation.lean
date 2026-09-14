import Reeken.Nonstandard.Shadow

/-! # Appreciable separation from a common shadow on a compact set

This is the compactness/saturation step in Section 3: away from the common shadow
of the two polygon arcs, a point cannot be infinitesimally close to both arcs.
-/

open Filter Set Metric

namespace Reeken.NSA

variable {E : Type*} [MetricSpace E] [Nonempty E]

/-- Outside a common shadow, compactness makes the exclusion of simultaneous proximity uniform. -/
theorem compact_separation_from_common_shadow {K : Set E} (hK : IsCompact K)
    {s t : ℕ → Set E} (hdis : Disjoint K (shadow s ∩ shadow t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ K, ∀ y ∈ s i, ∀ z ∈ t i, δ ≤ max (dist y x) (dist z x) := by
  by_contra h
  have hbad (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ i in hyperfilter ℕ,
      ∃ x ∈ K, ∃ y ∈ s i, ∃ z ∈ t i, dist y x < δ ∧ dist z x < δ := by
    have hn : ¬ ∀ᶠ i in hyperfilter ℕ,
        ∀ x ∈ K, ∀ y ∈ s i, ∀ z ∈ t i, δ ≤ max (dist y x) (dist z x) :=
      fun he ↦ h ⟨δ, hδ, he⟩
    filter_upwards [Ultrafilter.eventually_not.mpr hn] with i hi
    push Not at hi
    obtain ⟨x, hx, y, hy, z, hz, hd⟩ := hi
    exact ⟨x, hx, y, hy, z, hz, max_lt_iff.mp hd⟩
  let P (k i : ℕ) (w : E × E × E) : Prop :=
    w.1 ∈ K ∧ w.2.1 ∈ s i ∧ w.2.2 ∈ t i ∧
      dist w.2.1 w.1 < 1 / (k + 1 : ℝ) ∧ dist w.2.2 w.1 < 1 / (k + 1 : ℝ)
  have hfinite : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ w, ∀ k ≤ n, P k i w := by
    intro n
    filter_upwards [hbad (1 / (n + 1 : ℝ)) (by positivity)] with i hi
    obtain ⟨x, hx, y, hy, z, hz, hd, hd'⟩ := hi
    refine ⟨(x, y, z), fun k hk ↦ ⟨hx, hy, hz, hd.trans_le ?_, hd'.trans_le ?_⟩⟩ <;>
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hk 1)
  obtain ⟨w, hw⟩ := countable_saturation_of_eventually P hfinite
  star_cases w
  have hxK : ofSeq (U := hyperfilter ℕ) (fun i ↦ (w i).1) ∈ starSet K :=
    (hw 0).mono fun i hi ↦ hi.1
  obtain ⟨a, ha, hxa⟩ := compact_standard_part hK hxK
  have hyx : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (w i).2.1))
      (ofSeq (fun i ↦ (w i).1)) := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact (hw k).mono fun i hi ↦ hi.2.2.2.1.trans hk
  have hzx : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (w i).2.2))
      (ofSeq (fun i ↦ (w i).1)) := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact (hw k).mono fun i hi ↦ hi.2.2.2.2.trans hk
  apply Set.disjoint_left.mp hdis ha
  exact ⟨⟨ofSeq (fun i ↦ (w i).2.1), (hw 0).mono fun i hi ↦ hi.2.1, hyx.trans hxa⟩,
    ⟨ofSeq (fun i ↦ (w i).2.2), (hw 0).mono fun i hi ↦ hi.2.2.1, hzx.trans hxa⟩⟩

end Reeken.NSA
