import Reeken.Geometry.Segments
import Mathlib.Analysis.Normed.Module.Ray

/-! # The shortcut estimate for adjacent overlapping edges -/

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two consecutive edges that meet away from their common endpoint backtrack.
Deleting that endpoint cannot increase the maximum edge length. -/
theorem dist_le_max_of_adjacent_overlap {a b c x : E}
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ b c) (hxb : x ≠ b) :
    dist a c ≤ max (dist a b) (dist b c) := by
  have h₁ : SameRay ℝ (x - b) (a - b) := by
    simpa using ((mem_segment_iff_wbtw.mp hx).symm.sameRay_vsub_left)
  have h₂ : SameRay ℝ (x - b) (c - b) := by
    simpa using (mem_segment_iff_wbtw.mp hy).sameRay_vsub_left
  have hr := h₁.symm.trans h₂ (fun h ↦ (hxb (sub_eq_zero.mp h)).elim)
  have hn := hr.norm_sub
  rw [sub_sub_sub_cancel_right] at hn
  rw [dist_eq_norm, hn]
  apply abs_le.mpr
  constructor
  · have hc : ‖c - b‖ ≤ max (dist a b) (dist b c) := by
      simpa only [← dist_eq_norm, dist_comm c b] using le_max_right (dist a b) (dist b c)
    have ha := norm_nonneg (a - b)
    linarith
  · have ha : ‖a - b‖ ≤ max (dist a b) (dist b c) := by
      simpa only [← dist_eq_norm] using le_max_left (dist a b) (dist b c)
    have hc := norm_nonneg (c - b)
    linarith

end Reeken.Geometry
