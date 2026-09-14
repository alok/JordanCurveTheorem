import Reeken.Nonstandard.Metric
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

/-- The standard points infinitesimally close to some point of an internal set. -/
def shadow (s : ℕ → Set α) : Set α :=
  {a | ∃ x ∈ internalSet (U := hyperfilter ℕ) s, Near x (std a)}

/-- Saturation supplies one point realizing all the positive standard distance bounds. -/
theorem mem_shadow_iff (s : ℕ → Set α) (a : α) :
    a ∈ shadow s ↔ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in hyperfilter ℕ, ∃ x ∈ s i, dist x a < ε := by
  constructor
  · rintro ⟨x, hx, ha⟩ ε hε
    obtain ⟨x, rfl⟩ := ofSeq_surjective x
    filter_upwards [hx, ha ε hε] with i hi hd
    exact ⟨x i, hi, hd⟩
  · intro h
    let P (n i : ℕ) (x : α) : Prop := x ∈ s i ∧ dist x a < 1 / (n + 1 : ℝ)
    have hfinite : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ x, ∀ k ≤ n, P k i x := by
      intro n
      filter_upwards [h (1 / (n + 1 : ℝ)) (by positivity)] with i hi
      obtain ⟨x, hx, hd⟩ := hi
      refine ⟨x, fun k hk ↦ ⟨hx, hd.trans_le ?_⟩⟩
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    obtain ⟨x, hx⟩ := countable_saturation_of_eventually P hfinite
    obtain ⟨x, rfl⟩ := ofSeq_surjective x
    refine ⟨ofSeq x, (hx 0).mono fun i hi ↦ hi.1, ?_⟩
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (hx n).mono fun i hi ↦ hi.2.trans hn

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
