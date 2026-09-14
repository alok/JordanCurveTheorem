import Schoenflies.Square
import Mathlib.Order.Interval.Set.Infinite

/-! # Generic squares and the compact annulus used in Section 3 -/

open Set Metric Schoenflies

namespace Reeken.Geometry

/-- The boundary expressed by its sup-distance equation. -/
def squareBoundary (c : Plane) (r : ℝ) : Set Plane := {x | Plane.supDist x c = r}

/-- A fixed compact annulus contains the boundaries of all squares of the chosen scale. -/
def squareAnnulus (c : Plane) (r R : ℝ) : Set Plane :=
  Plane.closedSquare c R \ Plane.openSquare c r

theorem isCompact_closedSquare (c : Plane) (r : ℝ) :
    IsCompact (Plane.closedSquare c r) := by
  apply (isCompact_closedBall c (Real.sqrt 2 * r)).of_isClosed_subset
    (Plane.isClosed_closedSquare c r)
  intro x hx
  change dist x c ≤ Real.sqrt 2 * r
  rw [dist_eq_norm]
  exact (Plane.norm_le_sqrt_two_mul_supNorm (x - c)).trans
    (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))

theorem isCompact_squareAnnulus (c : Plane) (r R : ℝ) :
    IsCompact (squareAnnulus c r R) :=
  (isCompact_closedSquare c R).diff (Plane.isOpen_openSquare c r)

theorem squareBoundary_subset_annulus {c : Plane} {r R ρ : ℝ}
    (hr : r ≤ ρ) (hR : ρ ≤ R) : squareBoundary c ρ ⊆ squareAnnulus c r R := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change Plane.supDist x c ≤ R
    exact hx.trans_le hR
  · change ¬ Plane.supDist x c < r
    exact not_lt_of_ge (hr.trans_eq hx.symm)

theorem squareAnnulus_disjoint_endpoints {a b : Plane} {r R : ℝ}
    (hr : 0 < r) (hb : R < Plane.supDist b a) : Disjoint (squareAnnulus a r R) {a, b} := by
  rw [Set.disjoint_left]
  rintro x hx (rfl | rfl)
  · exact hx.2 (by simpa [Plane.openSquare] using hr)
  · exact (not_le_of_gt hb) hx.1

theorem continuous_supDist_left (c : Plane) : Continuous (fun x ↦ Plane.supDist x c) := by
  unfold Plane.supDist Plane.supNorm
  fun_prop

theorem supDist_pos_of_ne {a b : Plane} (hab : a ≠ b) : 0 < Plane.supDist a b := by
  apply lt_of_le_of_ne (Plane.supDist_nonneg a b)
  intro he
  have h := Plane.norm_le_sqrt_two_mul_supNorm (a - b)
  change ‖a - b‖ ≤ Real.sqrt 2 * Plane.supDist a b at h
  rw [← he, mul_zero] at h
  exact hab (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _))))

/-- Avoiding a finite set of vertex distances leaves a square at every positive scale. -/
theorem exists_generic_square_radius {ι : Type*} [Finite ι] (v : ι → Plane)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ ρ ∈ Ioo r (2 * r), ∀ i, v i ∉ squareBoundary c ρ := by
  have hi : (Ioo r (2 * r)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨ρ, hρ, hn⟩ := (hi.sdiff (Set.finite_range (fun i ↦ Plane.supDist (v i) c))).nonempty
  refine ⟨ρ, hρ, fun i he ↦ ?_⟩
  exact hn ⟨i, he⟩

/-- The local squares can be arbitrarily small and remain separated from a second cut point. -/
theorem exists_small_square_scale {a b : Plane} (hab : a ≠ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 2 * r < Plane.supDist b a ∧
      Plane.closedSquare a (2 * r) ⊆ ball a ε := by
  have hd := supDist_pos_of_ne hab.symm
  let r := min (ε / 8) (Plane.supDist b a / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : r ≤ ε / 8 := min_le_left _ _
  have hrd : r ≤ Plane.supDist b a / 4 := min_le_right _ _
  refine ⟨r, hr, by linarith, ?_⟩
  intro x hx
  have hnorm := Plane.norm_le_sqrt_two_mul_supNorm (x - a)
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hsup : Plane.supNorm (x - a) ≤ 2 * r := hx
  have hmul := mul_le_mul hsqrt hsup (Plane.supNorm_nonneg (x - a)) (by norm_num)
  change dist x a < ε
  rw [dist_eq_norm]
  linarith

end Reeken.Geometry
