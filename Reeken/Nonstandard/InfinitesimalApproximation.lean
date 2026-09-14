import Reeken.Nonstandard.Shadow

/-!
# A single infinitesimal bound for internal approximations

Saturation strengthens approximation at every standard scale into approximation by
one positive infinitesimal. This is the precise form needed in Kanovei–Reeken Lemma 1(ii).
-/

open Filter

namespace Reeken.NSA

variable {E : Type*} [PseudoMetricSpace E]

theorem exists_infinitesimal_hausdorff_bound {p q : ℕ → Set E}
    (hpq : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ p i, ∃ y ∈ q i, dist x y < ε)
    (hqp : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ y ∈ q i, ∃ x ∈ p i, dist x y < ε) :
    ∃ r : Star (hyperfilter ℕ) ℝ, Near r (std 0) ∧
      Holds (fun i ε ↦ 0 < ε ∧
        (∀ x ∈ p i, ∃ y ∈ q i, dist x y < ε) ∧
        (∀ y ∈ q i, ∃ x ∈ p i, dist x y < ε)) r := by
  let Q (i : ℕ) (ε : ℝ) := 0 < ε ∧
    (∀ x ∈ p i, ∃ y ∈ q i, dist x y < ε) ∧
    (∀ y ∈ q i, ∃ x ∈ p i, dist x y < ε)
  let P (n i : ℕ) (r : ℝ) := Q i r ∧ r ≤ 1 / (n + 1 : ℝ)
  have hfinite : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ r, ∀ k ≤ n, P k i r := by
    intro n
    have hn : 0 < 1 / (n + 1 : ℝ) := by positivity
    filter_upwards [hpq _ hn, hqp _ hn] with i hi hj
    refine ⟨1 / (n + 1 : ℝ), ?_⟩
    intro k hk
    exact ⟨⟨hn, hi, hj⟩, one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hk 1)⟩
  obtain ⟨r, hr⟩ := countable_saturation_of_eventually P hfinite
  star_cases r
  refine ⟨ofSeq r, ?_, (hr 0).mono fun i hi ↦ hi.1⟩
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  filter_upwards [hr n] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_pos hi.1.1]
  exact hi.2.trans_lt hn

end Reeken.NSA
