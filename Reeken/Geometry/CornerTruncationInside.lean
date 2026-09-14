import Reeken.Geometry.MaximalCornerVertex

/-! # Which side contains a corner truncation

At a strictly supported corner, a smaller triangle on the two incident rays has
the same inward unit bisector. If its interior avoids the polygon, that common
local point places its entire interior in the polygon's inside.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem unit_direction_smul_pos (v : Plane) {r : ℝ} (hr : 0 < r) :
    ‖r • v‖⁻¹ • (r • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul, Real.norm_of_nonneg hr.le, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hr), mul_one]

theorem unit_direction_lineMap (a b : Plane) {r : ℝ} (hr : 0 < r) :
    ‖AffineMap.lineMap a b r - a‖⁻¹ • (AffineMap.lineMap a b r - a) = ‖b - a‖⁻¹ • (b - a) := by
  have he : AffineMap.lineMap a b r - a = r • (b - a) := by
    rw [AffineMap.lineMap_apply_module]
    module
  rw [he, unit_direction_smul_pos _ hr]

theorem corner_truncation_inside {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3))
    (F : Plane →L[ℝ] ℝ) (hF : ∀ x ∈ P.carrier, F x ≤ F (P.vertex i))
    (hprev : F (P.vertex (i - 1)) < F (P.vertex i))
    (hnext : F (P.vertex (i + 1)) < F (P.vertex i))
    {r : ℝ} (hr : 0 < r)
    (hdisj : Disjoint (interior (convexHull ℝ {P.vertex i,
      AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r,
      AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r})) P.carrier) :
    interior (convexHull ℝ {P.vertex i,
      AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r,
      AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r}) ⊆ inside P.carrier := by
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  let T := Schoenflies.triangle (det_triangle_lineMap_ne_zero hdet (ne_of_gt hr))
  have hTi : inside T.carrier = interior (convexHull ℝ {P.vertex i,
      AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r,
      AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r}) := by
    rw [inside_triangle_eq_interior_hull, triangle_range_vertices]
  have ht : F (T.vertex 1) < F (T.vertex 0) := by
    change F (AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r) < F (P.vertex i)
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    nlinarith
  have hp : F (T.vertex (-1)) < F (T.vertex 0) := by
    change F (AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r) < F (P.vertex i)
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    nlinarith
  have hTF : ∀ x ∈ T.carrier, F x ≤ F (T.vertex 0) := by
    have hH : convexHull ℝ (range T.vertex) ⊆ {x | F x ≤ F (T.vertex 0)} := by
      rw [triangle_range_vertices]
      apply convexHull_min _ (convex_halfSpace_le
        (show IsLinearMap ℝ F from ⟨F.map_add, F.map_smul⟩) (F (T.vertex 0)))
      simp only [insert_subset_iff, singleton_subset_iff]
      change F (T.vertex 0) ≤ F (T.vertex 0) ∧ F (T.vertex 1) ≤ F (T.vertex 0) ∧
        F (T.vertex (-1)) ≤ F (T.vertex 0)
      exact ⟨le_rfl, ht.le, hp.le⟩
    exact (triangle_carrier_subset_hull T).trans hH
  have hdir : T.tang 0 + T.rayIn 0 = P.tang i + P.rayIn i := by
    congr 1
    · change ‖AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r - P.vertex i‖⁻¹ •
        (AffineMap.lineMap (P.vertex i) (P.vertex (i + 1)) r - P.vertex i) = _
      exact unit_direction_lineMap _ _ hr
    · change ‖AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r - P.vertex i‖⁻¹ •
        (AffineMap.lineMap (P.vertex i) (P.vertex (i - 1)) r - P.vertex i) = _
      exact unit_direction_lineMap _ _ hr
  obtain ⟨δP, hδP, hinP⟩ := exists_inward_bisector P i F hF hprev hnext
  obtain ⟨δT, hδT, hinT⟩ := exists_inward_bisector T 0 F hTF hp ht
  let ε := min δP δT / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεP : ε < δP := by dsimp [ε]; linarith [min_le_left δP δT]
  have hεT : ε < δT := by dsimp [ε]; linarith [min_le_right δP δT]
  have hbothT := hinT ε hε hεT
  rw [hdir] at hbothT
  rw [← hTi]
  apply T.isSeparating_carrier.isConnected_inside.isPreconnected.subset_left_of_subset_union
    P.isSeparating_carrier.isOpen_inside P.isSeparating_carrier.isOpen_outside disjoint_inside_outside
  · rw [inside_union_outside]
    rw [← hTi] at hdisj
    exact hdisj.subset_compl_right
  · exact ⟨_, hbothT, hinP ε hε hεP⟩

end Reeken.Geometry
