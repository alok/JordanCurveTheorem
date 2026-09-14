import Reeken.Geometry.CornerTruncationInside

/-! # Every nontriangular simple polygon has an internal diagonal

At a strictly exposed corner, an empty neighbor triangle supplies the diagonal
between the neighbors. Otherwise a maximal-height vertex supplies a diagonal
from the apex through an empty parallel truncation. Both endpoints are existing
polygon vertices, and they are not adjacent.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem exists_internal_diagonal {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m) :
    ∃ (i j : ZMod (m + 3)), j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      openSegment ℝ (P.vertex i) (P.vertex j) ⊆ inside P.carrier := by
  classical
  obtain ⟨i, F, hstrict, hF, -⟩ := exists_strictly_exposed_vertex P
  have hprev : F (P.vertex (i - 1)) < F (P.vertex i) :=
    hstrict _ (fun he ↦ ClosedPolygon.one_ne_zero' (m := m) (by linear_combination -he))
  have hnext : F (P.vertex (i + 1)) < F (P.vertex i) :=
    hstrict _ (ClosedPolygon.succ_ne_self i)
  by_cases hex : ∃ j, j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)}
  · obtain ⟨j, r, hr, hr1, hji, hjnext, hjprev, hjbase, hdisj⟩ :=
      exists_empty_corner_truncation P i hex
    refine ⟨i, j, hji, hjnext, hjprev, ?_⟩
    have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
      rw [Plane.det_comm]
      exact neg_ne_zero.mpr (P.corner i)
    exact (openSegment_apex_base_subset_interior
      (det_triangle_lineMap_ne_zero hdet (ne_of_gt hr)) hjbase).trans
      (corner_truncation_inside P i F hF hprev hnext hr hdisj)
  · have hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
        j = i ∨ j = i + 1 ∨ j = i - 1 := by
      intro j hj
      rw [cornerTriangle_range] at hj
      by_contra hn
      push Not at hn
      exact hex ⟨j, hn.1, hn.2.1, hn.2.2, hj⟩
    have hthree : (3 : ZMod (m + 3)) ≠ 0 := by
      intro he
      have hd : m + 3 ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (m + 3)).mp he
      have := Nat.le_of_dvd (by omega : 0 < 3) hd
      omega
    refine ⟨i - 1, i + 1, (Ne.symm (PrePolygon.pred_ne_succ i)), ?_, ?_, ?_⟩
    · intro he
      exact ClosedPolygon.one_ne_zero' (m := m) (by linear_combination he)
    · intro he
      exact hthree (by linear_combination he)
    · rw [openSegment_symm ℝ (P.vertex (i - 1)) (P.vertex (i + 1))]
      exact empty_corner_base_inside P hm i F hF hprev hnext hempty

end Reeken.Geometry
