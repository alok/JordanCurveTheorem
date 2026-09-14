import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Linarith

/-!
# Metric estimates for loop cutting

These estimates are the finite geometric calculation in Kanovei–Reeken Lemma 2.
They allow intersecting edges to be replaced without increasing the largest edge length.
-/

namespace Reeken.Geometry

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point on a segment is no farther from its left endpoint than the right endpoint is. -/
theorem dist_left_le_of_mem_segment {a b x : E} (hx : x ∈ segment ℝ a b) :
    dist a x ≤ dist a b := by
  have h := dist_add_dist_of_mem_segment hx
  have hn := dist_nonneg (x := x) (y := b)
  linarith

/-- The elementary inequality used in the loop-cutting construction, including degenerate edges. -/
theorem min_cross_dist_le_max_of_intersection {a b c d x : E}
    (hab : x ∈ segment ℝ a b) (hcd : x ∈ segment ℝ c d) :
    min (dist a c) (dist b d) ≤ max (dist a b) (dist c d) := by
  have hab' := dist_add_dist_of_mem_segment hab
  have hcd' := dist_add_dist_of_mem_segment hcd
  have hac := dist_triangle a x c
  have hbd := dist_triangle b x d
  rw [dist_comm x c] at hac
  rw [dist_comm b x] at hbd
  have hmax₁ := le_max_left (dist a b) (dist c d)
  have hmax₂ := le_max_right (dist a b) (dist c d)
  by_contra! h
  obtain ⟨h₁, h₂⟩ := lt_min_iff.mp h
  linarith

/-- One of the two possible replacement edges satisfies the same prescribed length bound. -/
theorem short_replacement_of_intersection {a b c d x : E} {ε : ℝ}
    (hab : x ∈ segment ℝ a b) (hcd : x ∈ segment ℝ c d)
    (h₁ : dist a b ≤ ε) (h₂ : dist c d ≤ ε) :
    dist a c ≤ ε ∨ dist b d ≤ ε := by
  exact min_le_iff.mp ((min_cross_dist_le_max_of_intersection hab hcd).trans
    (max_le h₁ h₂))

end Reeken.Geometry
