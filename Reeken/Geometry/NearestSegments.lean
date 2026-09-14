import Reeken.Geometry.Segments
import Mathlib.Analysis.Convex.StrictConvexBetween

/-! # Shortest boundary segments used in the inner-polygon construction -/

open Set

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E]

def IsNearest (s : Set E) (a b : E) : Prop :=
  b ∈ s ∧ ∀ c ∈ s, dist a b ≤ dist a c

theorem exists_nearest_of_isCompact {s : Set E} (hs : IsCompact s) (hne : s.Nonempty) (a : E) :
    ∃ b, IsNearest s a b := by
  obtain ⟨b, hb, hmin⟩ := hs.exists_isMinOn hne (continuous_const.dist continuous_id).continuousOn
  exact ⟨b, hb, hmin⟩

variable [NormedSpace ℝ E]

/-- Every point of a shortest segment has the same endpoint as a nearest point. -/
theorem IsNearest.on_segment {s : Set E} {a b x : E}
    (h : IsNearest s a b) (hx : x ∈ segment ℝ a b) : IsNearest s x b := by
  refine ⟨h.1, fun c hc ↦ ?_⟩
  have he := dist_add_dist_of_mem_segment hx
  have hmin := h.2 c hc
  have ht := dist_triangle a x c
  linarith

variable [StrictConvexSpace ℝ E]

/-- Before its boundary endpoint, a shortest segment has a unique nearest point.
Strict convexity is needed here, and holds for the Euclidean plane. -/
theorem IsNearest.unique_on_segment {s : Set E} {a b x c : E}
    (h : IsNearest s a b) (hx : x ∈ segment ℝ a b) (hxa : x ≠ a)
    (hc : c ∈ s) (hcx : dist x c ≤ dist x b) : c = b := by
  have hxb := h.on_segment hx
  have hd : dist x c = dist x b := le_antisymm hcx (hxb.2 c hc)
  have he := dist_add_dist_of_mem_segment hx
  have ht := dist_triangle a x c
  have hmin := h.2 c hc
  have hac : dist a x + dist x c = dist a c := by linarith
  have hbRay : SameRay ℝ (x - a) (b - x) := by
    simpa using (mem_segment_iff_wbtw.mp hx).sameRay_vsub
  have hcRay : SameRay ℝ (x - a) (c - x) := by
    simpa using (dist_add_dist_eq_iff.mp hac).sameRay_vsub
  have hbc := hcRay.symm.trans hbRay (fun hz ↦ (hxa (sub_eq_zero.mp hz)).elim)
  have hnorm : ‖c - x‖ = ‖b - x‖ := by
    simpa only [← dist_eq_norm, dist_comm c x, dist_comm b x] using hd
  exact sub_left_injective (hbc.eq_of_norm_eq hnorm)

/-- Shortest boundary segments meeting beyond their initial points have the same foot. -/
theorem nearest_segments_common_foot {s : Set E} {a b c d x : E}
    (hab : IsNearest s a b) (hcd : IsNearest s c d)
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ c d) (hxa : x ≠ a) : d = b :=
  hab.unique_on_segment hx hxa hcd.1 ((hcd.on_segment hy).2 b hab.1)

/-- Two shortest boundary segments cannot have a proper interior crossing. -/
theorem nearest_segments_no_inner_crossing {s : Set E} {a b c d x : E}
    (hab : IsNearest s a b) (hcd : IsNearest s c d)
    (hx : Sbtw ℝ a x b) (hy : Sbtw ℝ c x d)
    (hinter : segment ℝ a b ∩ segment ℝ c d = {x}) : False := by
  have hdb := nearest_segments_common_foot hab hcd hx.wbtw.mem_segment hy.wbtw.mem_segment hx.ne_left
  have hb : b ∈ segment ℝ a b ∩ segment ℝ c d := by
    rw [hdb]
    exact ⟨right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
  rw [hinter, mem_singleton_iff] at hb
  exact hx.ne_right hb.symm

end Reeken.Geometry
