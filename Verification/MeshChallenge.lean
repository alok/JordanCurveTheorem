import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Order.Filter.Ultrafilter.Basic

open Filter Set

namespace Verification

universe u

/-- Independent sequence formulation, with the sampled segments written out explicitly. -/
theorem inscribed_mesh_shadow {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 1)) (a : E) :
    (∃ x : ℕ → E,
      (∀ᶠ n in hyperfilter ℕ, x n ∈ ⋃ k : Fin (n + 1),
        segment ℝ (f ((k : ℕ) / (n + 1 : ℝ))) (f (((k : ℕ) + 1) / (n + 1 : ℝ)))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in hyperfilter ℕ, dist (x n) a < ε) ↔
      a ∈ f '' Icc 0 1 := by
  sorry

end Verification
