import Reeken.Geometry.SegmentCollinearity

/-! # Segments touching a triangle's base

A segment through an interior point of the base either enters the triangle's
interior or lies on the base's line. If its endpoints also avoid the open base,
it must cover that base.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem triangleWeight_nonpos_of_segment_avoids {a b c p q x y : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hx : x ∈ openSegment ℝ b c)
    (hxseg : x ∈ segment ℝ p q) (hyseg : y ∈ segment ℝ p q)
    (havoid : Disjoint (segment ℝ p q) (interior (convexHull ℝ {a, b, c}))) :
    triangleWeights a b c y 0 ≤ 0 := by
  by_contra hn
  obtain ⟨δ, hδ, hδin⟩ := exists_motion_from_base_into_triangle h hx (lt_of_not_ge hn)
  let ε := min δ 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ 1]
  have hε1 : ε < 1 := by dsimp [ε]; linarith [min_le_right δ 1]
  have hr : (1 - ε) • x + ε • y ∈ segment ℝ p q :=
    (convex_segment p q) hxseg hyseg (by linarith) hε.le (by ring)
  exact disjoint_left.mp havoid hr (hδin ε hε hεδ)

theorem segment_base_subset_of_avoids_triangle {a b c p q x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hbc : b ≠ c)
    (hx : x ∈ openSegment ℝ b c) (hxseg : x ∈ openSegment ℝ p q)
    (hpout : p ∉ openSegment ℝ b c) (hqout : q ∉ openSegment ℝ b c)
    (havoid : Disjoint (segment ℝ p q) (interior (convexHull ℝ {a, b, c}))) :
    segment ℝ b c ⊆ segment ℝ p q := by
  have hxclosed := openSegment_subset_segment ℝ p q hxseg
  have hp := triangleWeight_nonpos_of_segment_avoids h hx hxclosed
    (left_mem_segment ℝ p q) havoid
  have hq := triangleWeight_nonpos_of_segment_avoids h hx hxclosed
    (right_mem_segment ℝ p q) havoid
  have hxseg' := hxseg
  obtain ⟨u, v, hu, hv, huv, he⟩ := hxseg
  have hew := congrArg (fun z ↦ triangleWeights a b c z 0) he
  rw [triangleWeights_combo a b c p q u v huv] at hew
  have hx0 := (triangleWeights_on_base h hx).1
  rw [hx0] at hew
  have hp0 : triangleWeights a b c p 0 = 0 := by
    have hvq : v * triangleWeights a b c q 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv.le hq
    nlinarith
  have hq0 : triangleWeights a b c q 0 = 0 := by
    rw [hp0, mul_zero, zero_add] at hew
    exact (mul_eq_zero.mp hew).resolve_left (ne_of_gt hv)
  exact segment_subset_of_lineMap_of_ends_outside hbc
    ⟨_, eq_lineMap_of_triangleWeight_zero h hp0⟩
    ⟨_, eq_lineMap_of_triangleWeight_zero h hq0⟩ hx hxseg' hpout hqout

end Reeken.Geometry
