import Reeken.Geometry.TriangleCoordinates

/-! # Triangle coordinates on the closed hull

Nonnegative coordinates characterize the closed triangle. A vanishing coordinate
places the point on the opposite edge. These facts locate polygon vertices in a
neighbor triangle without assuming they are in general position.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem triangleWeights_nonneg_of_mem_hull {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hx : x ∈ convexHull ℝ {a, b, c}) :
    ∀ i, 0 ≤ triangleWeights a b c x i := by
  intro i
  have hc : Convex ℝ {y | 0 ≤ triangleWeights a b c y i} := by
    intro p hp q hq u v hu hv huv
    change 0 ≤ triangleWeights a b c (u • p + v • q) i
    rw [triangleWeights_combo a b c p q u v huv]
    exact add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)
  have hv : {a, b, c} ⊆ {y | 0 ≤ triangleWeights a b c y i} := by
    have he : ∀ j : Fin 3, 0 ≤ triangleWeights a b c (![a, b, c] j) i := by
      intro j
      rw [triangleWeights_vertices h]
      split_ifs <;> norm_num
    rintro y (rfl | rfl | rfl)
    · exact he 0
    · exact he 1
    · exact he 2
  exact convexHull_min hv hc hx

theorem mem_triangle_hull_iff_weights_nonneg {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) :
    x ∈ convexHull ℝ {a, b, c} ↔ ∀ i, 0 ≤ triangleWeights a b c x i :=
  ⟨triangleWeights_nonneg_of_mem_hull h, mem_triangle_hull_of_weights_nonneg h⟩

theorem mem_triangle_edge_of_weight_zero {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hx : x ∈ convexHull ℝ {a, b, c})
    (i : Fin 3) (hi : triangleWeights a b c x i = 0) :
    x ∈ ![segment ℝ b c, segment ℝ a c, segment ℝ a b] i := by
  have hn := triangleWeights_nonneg_of_mem_hull h hx
  have hs := triangleWeights_sum h x
  have hd := triangleWeights_decompose h x
  simp [Fin.sum_univ_succ] at hs hd
  fin_cases i
  · change triangleWeights a b c x 0 = 0 at hi
    simp only [hi, zero_smul, zero_add] at hs hd
    exact ⟨_, _, hn 1, hn 2, hs, hd⟩
  · change triangleWeights a b c x 1 = 0 at hi
    simp only [hi, zero_smul, zero_add] at hs hd
    exact ⟨_, _, hn 0, hn 2, hs, hd⟩
  · change triangleWeights a b c x 2 = 0 at hi
    simp only [hi, zero_smul, add_zero] at hs hd
    exact ⟨_, _, hn 0, hn 1, hs, hd⟩

theorem openSegment_apex_base_subset_interior {a b c d : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hd : d ∈ openSegment ℝ b c) :
    openSegment ℝ a d ⊆ interior (convexHull ℝ {a, b, c}) := by
  obtain ⟨hd0, hd1, hd2⟩ := triangleWeights_on_base h hd
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  apply mem_interior_triangle_hull_of_weights_pos h
  intro i
  rw [triangleWeights_combo a b c a d u v huv]
  have ha := triangleWeights_vertices h 0 i
  change triangleWeights a b c a i = if (0 : Fin 3) = i then 1 else 0 at ha
  rw [ha]
  fin_cases i
  · simpa [hd0] using hu
  · simpa [Fin.ext_iff] using mul_pos hv hd1
  · simpa [Fin.ext_iff] using mul_pos hv hd2

end Reeken.Geometry
