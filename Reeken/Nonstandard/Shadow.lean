import Reeken.Nonstandard.InternalMetric
import Reeken.Nonstandard.Saturation
import Mathlib.Tactic.Positivity

/-!
# Standard shadows of internal sets

Countable saturation turns arbitrarily small standard-scale distances into a single
infinitesimally close internal witness. Consequently, standard shadows are closed and
points outside a shadow have an appreciable distance from the entire internal set.
-/

open Filter Topology Metric

namespace Reeken.NSA

variable {α : Type*} [MetricSpace α] [Nonempty α]

/-- Saturation realizes all standard neighborhoods by one internal point of the set.
The theorem works over any free ultrafilter on naturals. -/
theorem InternalSet.mem_shadow_iff_internal_ball {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ atTop) (s : InternalSet U α) (a : α) :
    a ∈ s.shadow ↔ ∀ ε : ℝ, 0 < ε →
      (s.toSet ∩ starSet (Metric.ball a ε)).Nonempty := by
  constructor
  · rintro ⟨x, hx, ha⟩ ε hε
    exact ⟨x, hx, (mem_starSet_ball x a ε).mpr (ha ε hε)⟩
  · intro h
    let q (n : ℕ) : InternalSet U α := s ⊓ std (Metric.ball a (1 / (n + 1 : ℝ)))
    have hfinite : ∀ n, ∃ x : Star U α, ∀ k ≤ n, x ∈ q k := by
      intro n
      obtain ⟨x, hxs, hxb⟩ := h (1 / (n + 1 : ℝ)) (by positivity)
      refine ⟨x, fun k hk ↦ ?_⟩
      change x ∈ InternalSet.toSet (s ⊓ std (Metric.ball a (1 / (k + 1 : ℝ))))
      rw [coe_inf, coe_std]
      refine ⟨hxs, starSet_mono (Metric.ball_subset_ball ?_) hxb⟩
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    obtain ⟨x, hx⟩ := InternalSet.countable_saturation hU q hfinite
    have hmem (n : ℕ) : x ∈ s.toSet ∩ starSet (Metric.ball a (1 / (n + 1 : ℝ))) := by
      have hx' : x ∈ (q n).toSet := hx n
      simpa only [q, coe_inf, coe_std] using hx'
    refine ⟨x, (hmem 0).1, fun ε hε ↦ ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (mem_starSet_ball x a ε).mp
      (starSet_mono (Metric.ball_subset_ball hn.le) (hmem n).2)

/-- The standard points infinitesimally close to some point of an internal set. -/
def shadow (s : ℕ → Set α) : Set α :=
  InternalSet.shadow (ofSeq (U := hyperfilter ℕ) s)

/-- Saturation supplies one point realizing all the positive standard distance bounds. -/
theorem mem_shadow_iff (s : ℕ → Set α) (a : α) :
    a ∈ shadow s ↔ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in hyperfilter ℕ, ∃ x ∈ s i, dist x a < ε := by
  rw [shadow, InternalSet.mem_shadow_iff_internal_ball Nat.hyperfilter_le_atTop]
  simp only [InternalSet.coe_ofSeq, starSet, ← internalSet_inter, internalSet_nonempty]
  rfl

/-- Failure of infinitesimal proximity gives a uniform positive standard distance bound. -/
theorem not_mem_shadow_iff (s : ℕ → Set α) (a : α) :
    a ∉ shadow s ↔ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ s i, ε ≤ dist x a := by
  rw [mem_shadow_iff]
  push Not
  rfl

/-- Standard shadows of internal sets are closed in a countably saturated metric model. -/
theorem isClosed_shadow (s : ℕ → Set α) : IsClosed (shadow s) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro a ha
  obtain ⟨ε, hε, h⟩ := (not_mem_shadow_iff s a).mp ha
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro b hb
  apply (not_mem_shadow_iff s b).mpr
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [h] with i hi
  intro x hx
  have hd := hi x hx
  have ht := dist_triangle x b a
  have hb' : dist b a < ε / 2 := hb
  linarith

omit [Nonempty α] in
/-- The shadow of a standard closed set is exactly that set. -/
theorem shadow_const_of_isClosed {s : Set α} (hs : IsClosed s) :
    shadow (fun _ ↦ s) = s := by
  ext a
  constructor
  · rintro ⟨x, hx, ha⟩
    exact closed_standard_part hs hx ha
  · intro ha
    exact ⟨std a, (std_mem_starSet s a).mpr ha, Near.refl _⟩

end Reeken.NSA
