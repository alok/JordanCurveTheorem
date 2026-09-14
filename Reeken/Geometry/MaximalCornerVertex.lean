import Reeken.Geometry.CornerVisibility
import Reeken.Geometry.DiagonalDeletion

/-! # The highest vertex in an occupied neighbor triangle

A polygon vertex in its neighbor triangle, distinct from the three corners, has
positive coordinates along both adjacent sides. Choosing one of maximal height
gives a parallel truncation whose interior contains no polygon edge.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem corner_weights_pos_of_other_vertex {m : ℕ} (P : ClosedPolygon m)
    (i j : ZMod (m + 3)) (hji : j ≠ i) (hjnext : j ≠ i + 1) (hjprev : j ≠ i - 1)
    (hj : P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)}) :
    0 < triangleWeights (P.vertex i) (P.vertex (i + 1)) (P.vertex (i - 1)) (P.vertex j) 1 ∧
    0 < triangleWeights (P.vertex i) (P.vertex (i + 1)) (P.vertex (i - 1)) (P.vertex j) 2 := by
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  have hn := triangleWeights_nonneg_of_mem_hull hdet hj
  constructor
  · by_contra hn1
    have hz : triangleWeights (P.vertex i) (P.vertex (i + 1)) (P.vertex (i - 1)) (P.vertex j) 1 = 0 :=
      le_antisymm (le_of_not_gt hn1) (hn 1)
    have hseg := mem_triangle_edge_of_weight_zero hdet hj 1 hz
    have hedge : P.vertex j ∈ P.toPre.edge (i - 1) := by
      change P.vertex j ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
      rw [sub_add_cancel, segment_symm]
      exact hseg
    have he := prePolygon_vertex_mem_edge_ends P.toPre hedge
    change P.vertex j = P.vertex (i - 1) ∨ P.vertex j = P.vertex (i - 1 + 1) at he
    rw [sub_add_cancel] at he
    exact he.elim (fun he ↦ hjprev (P.vertex_inj he)) (fun he ↦ hji (P.vertex_inj he))
  · by_contra hn2
    have hz : triangleWeights (P.vertex i) (P.vertex (i + 1)) (P.vertex (i - 1)) (P.vertex j) 2 = 0 :=
      le_antisymm (le_of_not_gt hn2) (hn 2)
    have hseg := mem_triangle_edge_of_weight_zero hdet hj 2 hz
    have he := prePolygon_vertex_mem_edge_ends P.toPre hseg
    exact he.elim (fun he ↦ hji (P.vertex_inj he)) (fun he ↦ hjnext (P.vertex_inj he))

theorem exists_empty_corner_truncation {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3))
    (hex : ∃ j, j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)}) :
    ∃ (j : ZMod (m + 3)) (r : ℝ), 0 < r ∧ r ≤ 1 ∧ j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      P.vertex j ∈ openSegment ℝ (AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r)
        (AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r) ∧
      Disjoint (interior (convexHull ℝ {P.vertex i,
        AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r,
        AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r})) P.carrier := by
  classical
  let S : Finset (ZMod (m + 3)) := Finset.univ.filter fun j ↦ j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
    P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)}
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, by simpa [S] using hj⟩
  let w := triangleWeights (P.vertex i) (P.vertex (i + 1)) (P.vertex (i - 1))
  obtain ⟨j, hjS, hmax⟩ := S.exists_max_image (fun j ↦ w (P.vertex j) 0) hS
  have hj : j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} := by
    simpa [S] using hjS
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  obtain ⟨hj1, hj2⟩ := corner_weights_pos_of_other_vertex P i j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
  have hj0 : 0 ≤ w (P.vertex j) 0 := triangleWeights_nonneg_of_mem_hull hdet hj.2.2.2 0
  have hsum := triangleWeights_sum hdet (P.vertex j)
  simp [Fin.sum_univ_succ] at hsum
  let r := 1 - w (P.vertex j) 0
  have hr : 0 < r := by dsimp [r, w]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hheight : ∀ k, k ≠ i →
      P.vertex k ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} →
      w (P.vertex k) 0 ≤ w (P.vertex j) 0 := by
    intro k hki hk
    by_cases hkn : k = i + 1
    · rw [hkn]
      have he := triangleWeights_vertices hdet 1 0
      norm_num [Fin.ext_iff] at he
      change w (P.vertex (i + 1)) 0 = 0 at he
      rw [he]
      exact hj0
    by_cases hkp : k = i - 1
    · rw [hkp]
      have he := triangleWeights_vertices hdet 2 0
      norm_num [Fin.ext_iff] at he
      change w (P.vertex (i - 1)) 0 = 0 at he
      rw [he]
      exact hj0
    exact hmax k (by simp [S, hki, hkn, hkp, hk])
  have hsmall := det_triangle_lineMap_ne_zero hdet (ne_of_gt hr)
  refine ⟨j, r, hr, hr1, hj.1, hj.2.1, hj.2.2.1, ?_, ?_⟩
  · exact mem_open_truncated_base_of_height hdet hr (by dsimp [r, w]; ring) hj1 hj2
  · have hd := corner_triangle_disjoint_carrier_of_vertices_on_base P i
      (lineMap_mem_segment ℝ _ _ ⟨hr.le, hr1⟩)
      (by rw [segment_symm]; exact lineMap_mem_segment ℝ _ _ ⟨hr.le, hr1⟩) hsmall
      (fun k hki hk ↦ ?_)
    · rw [inside_triangle_eq_interior_hull, triangle_range_vertices] at hd
      exact hd
    have hkbig := truncated_triangle_hull_subset ⟨hr.le, hr1⟩ hk
    have hkmax := hheight k hki hkbig
    have hk0 := triangleWeights_nonneg_of_mem_hull hsmall hk 0
    rw [triangleWeights_lineMap hdet (ne_of_gt hr)] at hk0
    simp only [ite_true] at hk0
    have hkge := (le_div_iff₀ hr).mp hk0
    simp only [zero_mul] at hkge
    apply mem_truncated_base_of_height hdet hr hkbig
    dsimp [r] at hkge ⊢
    change w (P.vertex k) 0 = _
    linarith

end Reeken.Geometry
