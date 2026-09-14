import Reeken.Geometry.TriangleWeightsHull

/-! # A triangle cut by a line parallel to its base

Moving both base vertices the same fraction of the way from the apex gives a
smaller triangle. Its coordinates isolate vertices of maximal height in the
original triangle.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem det_triangle_lineMap (a b c : Plane) (r : ℝ) :
    Plane.det (AffineMap.lineMap a b r - a) (AffineMap.lineMap a c r - a) =
      r ^ 2 * Plane.det (b - a) (c - a) := by
  simp [AffineMap.lineMap_apply_module, Plane.det]
  ring

theorem det_triangle_lineMap_ne_zero {a b c : Plane} {r : ℝ}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hr : r ≠ 0) :
    Plane.det (AffineMap.lineMap a b r - a) (AffineMap.lineMap a c r - a) ≠ 0 := by
  rw [det_triangle_lineMap]
  exact mul_ne_zero (pow_ne_zero _ hr) h

theorem triangleWeights_lineMap {a b c : Plane} {r : ℝ}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hr : r ≠ 0) (x : Plane) (i : Fin 3) :
    triangleWeights a (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) x i =
      if i = 0 then (triangleWeights a b c x 0 - (1 - r)) / r
      else triangleWeights a b c x i / r := by
  fin_cases i <;> simp [triangleWeights, Fin.ext_iff, det_triangle_lineMap]
  all_goals
    field_simp [hr, h]
    simp [AffineMap.lineMap_apply_module, Plane.det]
    ring

theorem truncated_triangle_hull_subset {a b c : Plane} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    convexHull ℝ {a, AffineMap.lineMap a b r, AffineMap.lineMap a c r} ⊆
      convexHull ℝ {a, b, c} := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  simp only [insert_subset_iff, singleton_subset_iff]
  refine ⟨subset_convexHull ℝ _ (by simp), ?_, ?_⟩
  · exact segment_subset_convexHull (by simp) (by simp) (lineMap_mem_segment ℝ a b hr)
  · exact segment_subset_convexHull (by simp) (by simp) (lineMap_mem_segment ℝ a c hr)

theorem mem_truncated_base_of_height {a b c x : Plane} {r : ℝ}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hr : 0 < r)
    (hx : x ∈ convexHull ℝ {a, b, c}) (hxheight : triangleWeights a b c x 0 = 1 - r) :
    x ∈ segment ℝ (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) := by
  have hsmall := det_triangle_lineMap_ne_zero h (ne_of_gt hr)
  have hn := triangleWeights_nonneg_of_mem_hull h hx
  have hsmallHull : x ∈ convexHull ℝ {a, AffineMap.lineMap a b r, AffineMap.lineMap a c r} := by
    apply mem_triangle_hull_of_weights_nonneg hsmall
    intro i
    rw [triangleWeights_lineMap h (ne_of_gt hr)]
    split_ifs with hi
    · rw [hxheight, sub_self, zero_div]
    · exact div_nonneg (hn i) hr.le
  apply mem_triangle_edge_of_weight_zero hsmall hsmallHull 0
  rw [triangleWeights_lineMap h (ne_of_gt hr)]
  simp [hxheight]

theorem mem_open_truncated_base_of_height {a b c x : Plane} {r : ℝ}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hr : 0 < r)
    (hxheight : triangleWeights a b c x 0 = 1 - r)
    (hx1 : 0 < triangleWeights a b c x 1) (hx2 : 0 < triangleWeights a b c x 2) :
    x ∈ openSegment ℝ (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) := by
  have hsmall := det_triangle_lineMap_ne_zero h (ne_of_gt hr)
  have hs := triangleWeights_sum hsmall x
  have hd := triangleWeights_decompose hsmall x
  have h0 : triangleWeights a (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) x 0 = 0 := by
    rw [triangleWeights_lineMap h (ne_of_gt hr)]
    simp [hxheight]
  have h1 : 0 < triangleWeights a (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) x 1 := by
    rw [triangleWeights_lineMap h (ne_of_gt hr)]
    simpa [Fin.ext_iff] using div_pos hx1 hr
  have h2 : 0 < triangleWeights a (AffineMap.lineMap a b r) (AffineMap.lineMap a c r) x 2 := by
    rw [triangleWeights_lineMap h (ne_of_gt hr)]
    simpa [Fin.ext_iff] using div_pos hx2 hr
  simp [Fin.sum_univ_succ] at hs hd
  simp only [h0, zero_smul, zero_add] at hs hd
  exact ⟨_, _, h1, h2, hs, hd⟩

end Reeken.Geometry
