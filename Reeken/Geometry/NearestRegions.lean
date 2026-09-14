import Reeken.Geometry.NearestSegments
import Schoenflies.CrosscutCells
import Mathlib.Analysis.Convex.PathConnected

/-! # Shortest boundary connections stay in their starting region -/

open Set Schoenflies

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A shortest connection meets the target set only at its foot. -/
theorem IsNearest.segment_sdiff_subset_compl {C : Set E} {a b : E} (h : IsNearest C a b) :
    segment ℝ a b \ {b} ⊆ Cᶜ := by
  rintro x ⟨hx, hxb⟩ hxC
  have hd := (h.on_segment hx).2 x hxC
  rw [dist_self] at hd
  exact hxb (dist_le_zero.mp hd)

/-- Before reaching its foot, the whole shortest connection remains in one component. -/
theorem IsNearest.segment_sdiff_subset_component {C : Set E} {a b : E}
    (h : IsNearest C a b) : segment ℝ a b \ {b} ⊆ connectedComponentIn Cᶜ a := by
  rintro x ⟨hx, hxb⟩
  have hshort : dist a x < dist a b := by
    have hdist := dist_add_dist_of_mem_segment hx
    have hpos : 0 < dist x b := dist_pos.mpr hxb
    linarith
  have hsub : segment ℝ a x ⊆ Cᶜ := by
    intro y hy hyC
    have hle := dist_left_le_of_mem_segment hy
    have hmin := h.2 y hyC
    linarith
  exact ((convex_segment a x).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ a x) hsub) (right_mem_segment ℝ a x)

/-- This applies to the actual polygon side in which the rectangle vertex lies. -/
theorem IsNearest.segment_sdiff_subset_region {C Ω : Set Plane} {a b : Plane}
    (h : IsNearest C a b) (hC : IsSeparating C) (hΩ : IsRegionOf C Ω) (ha : a ∈ Ω) :
    segment ℝ a b \ {b} ⊆ Ω := by
  rw [← hΩ.connectedComponentIn_eq hC ha]
  exact h.segment_sdiff_subset_component

end Reeken.Geometry
