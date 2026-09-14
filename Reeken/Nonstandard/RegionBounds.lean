import Reeken.Geometry.ExteriorBounds
import Reeken.Geometry.PolygonTopology
import Reeken.Nonstandard.StandardRegions

/-! # Bounded standard inside and unbounded standard outside

The same standard square contains every inscribed polygon and every bounded
complementary component. Its exterior lies deeply in the internal outside.
These bounds do not depend on the common-boundary construction.
-/

open Filter Metric Set
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

theorem exists_uniform_square_bound (f : SimpleLoop Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : InscribedPolygon f, p.trace ⊆ Plane.closedSquare 0 r := by
  obtain ⟨r, hr, h⟩ := InscribedPolygon.exists_uniform_trace_bound f
  refine ⟨r, hr, fun p x hx ↦ ?_⟩
  have hn : ‖x‖ ≤ r := by simpa using h p hx
  change Plane.supDist x 0 ≤ r
  rw [Plane.supDist_zero]
  exact (Plane.supNorm_le_norm x).trans hn

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)

theorem beyondSquare_subset_standardOutside {r : ℝ}
    (h : ∀ i, (p i).trace ⊆ Plane.closedSquare 0 r) :
    Plane.beyondSquare r ⊆ standardOutside p := by
  intro a ha
  have hop : IsOpen (Plane.beyondSquare r) := by
    rw [Plane.beyondSquare_eq_compl]
    exact (Plane.isClosed_closedSquare 0 r).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hop a ha
  refine (mem_deep_iff _ a).mpr ⟨ε, hε, Eventually.of_forall fun i x hx ↦ ?_⟩
  apply le_of_not_gt
  intro hdist
  exact hx (beyondSquare_subset_outside (h i) (hball hdist))

theorem standardInside_subset_closedSquare {r : ℝ}
    (h : ∀ i, (p i).trace ⊆ Plane.closedSquare 0 r) :
    standardInside p ⊆ Plane.closedSquare 0 r := by
  intro a ha
  obtain ⟨i, hi⟩ := (eventually_mem_of_mem_deep ha).exists
  exact inside_subset_closedSquare (h i) hi

theorem isBounded_standardInside : Bornology.IsBounded (standardInside p) := by
  obtain ⟨r, _, h⟩ := exists_uniform_square_bound f
  refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt 2 * r, fun x hx ↦ ?_⟩
  have hs := standardInside_subset_closedSquare p (fun i ↦ h (p i)) hx
  have hsup : Plane.supNorm x ≤ r := by simpa [Plane.closedSquare] using hs
  exact (Plane.norm_le_sqrt_two_mul_supNorm x).trans
    (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _))

theorem not_isBounded_standardOutside : ¬ Bornology.IsBounded (standardOutside p) := by
  obtain ⟨r, _, h⟩ := exists_uniform_square_bound f
  exact fun hb ↦ not_isBounded_beyondSquare r
    (hb.subset (beyondSquare_subset_standardOutside p (fun i ↦ h (p i))))

/-- One ordinary real radius bounds every point of the standard inside. -/
theorem exists_standardInside_radius :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ standardInside p, ‖x‖ ≤ R :=
  (isBounded_standardInside p).exists_pos_norm_le

/-- The standard outside contains points beyond every prescribed real radius. -/
theorem exists_standardOutside_beyond (R : ℝ) :
    ∃ x ∈ standardOutside p, R < ‖x‖ := by
  by_contra h
  push Not at h
  exact not_isBounded_standardOutside p (isBounded_iff_forall_norm_le.mpr ⟨R, h⟩)

theorem standardOutside_nonempty : (standardOutside p).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h ↦
    not_isBounded_standardOutside p (h ▸ Bornology.isBounded_empty)

end Reeken.NSA
