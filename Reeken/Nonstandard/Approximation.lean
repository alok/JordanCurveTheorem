import Reeken.Nonstandard.Shadow

/-!
# Two-sided approximation and standard shadows

This converts ordinary estimates at every positive scale into the exact statement
that an internal approximation has the given standard shadow.
-/

open Filter Metric Set

namespace Reeken.NSA

variable {E : Type*} [MetricSpace E] [Nonempty E]

/-- Uniform infinitesimal proximity to another internal set gives inclusion of shadows. -/
theorem shadow_subset_of_approximation {p q : ℕ → Set E}
    (hpq : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ p i, ∃ y ∈ q i, dist x y < ε) : shadow p ⊆ shadow q := by
  intro a ha
  apply (mem_shadow_iff q a).mpr
  intro ε hε
  filter_upwards [(mem_shadow_iff p a).mp ha (ε / 2) (half_pos hε),
    hpq (ε / 2) (half_pos hε)] with i hai hi
  obtain ⟨x, hx, hxa⟩ := hai
  obtain ⟨y, hy, hxy⟩ := hi x hx
  refine ⟨y, hy, ?_⟩
  have h := dist_triangle y x a
  rw [dist_comm y x] at h
  linarith

/-- Two-sided approximation of a closed set identifies the shadow exactly. -/
theorem shadow_eq_of_approximation {p : ℕ → Set E} {c : Set E} (hc : IsClosed c)
    (hpc : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ p i, ∃ y ∈ c, dist x y < ε)
    (hcp : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ y ∈ c, ∃ x ∈ p i, dist x y < ε) : shadow p = c := by
  ext a
  constructor
  · intro ha
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have ha' := (mem_shadow_iff p a).mp ha (ε / 2) (half_pos hε)
    have hclose : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∃ y ∈ c, dist a y < ε := by
      filter_upwards [ha', hpc (ε / 2) (half_pos hε)] with i hai hpi
      obtain ⟨x, hx, hxa⟩ := hai
      obtain ⟨y, hy, hxy⟩ := hpi x hx
      refine ⟨y, hy, ?_⟩
      have ht := dist_triangle a x y
      rw [dist_comm a x] at ht
      linarith
    exact hclose.exists.choose_spec
  · intro ha
    apply (mem_shadow_iff p a).mpr
    intro ε hε
    exact (hcp ε hε).mono fun i hi ↦ hi a ha

end Reeken.NSA
