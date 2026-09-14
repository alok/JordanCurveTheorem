import Reeken.Nonstandard.OuterCell
import Reeken.Nonstandard.OuterContainment
import Reeken.Nonstandard.RegionBounds

/-! # One outer polygon contains every standard outside point in its outside

Uniform boundedness supplies one standard point far outside the outer polygon.
Infinitesimal barriers put every other standard outside point on the same side.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem exists_internal_outer_polygon :
    ∃ q : ℕ → Σ m, ClosedPolygon m,
      (∀ᶠ i in hyperfilter ℕ,
        (q i).2.carrier ⊆ outside (p i).trace ∧ outside (q i).2.carrier ⊆ outside (p i).trace ∧
        closure (outside (q i).2.carrier) ⊆ (f '' Icc 0 1)ᶜ) ∧
      shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 ∧
      standardOutside p ⊆ deep (fun i ↦ outside (q i).2.carrier) := by
  obtain ⟨q, hq, hshadow, hnear⟩ := exists_internal_outer_cell p hmax hs
  obtain ⟨r, hr, hbound⟩ := InscribedPolygon.exists_uniform_trace_bound f
  have hPbound : ∀ i, (p i).trace ⊆ Plane.closedSquare 0 r := by
    intro i x hx
    change Plane.supDist x 0 ≤ r
    rw [Plane.supDist_zero]
    exact (Plane.supNorm_le_norm x).trans (by simpa using hbound (p i) hx)
  have hQbound : ∀ᶠ i in hyperfilter ℕ, (q i).2.carrier ⊆ Plane.closedSquare 0 (r + 1) := by
    filter_upwards [hnear 1 zero_lt_one] with i hi
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hi x hx
    have hybound : ‖y‖ ≤ r := by simpa using hbound (p i) hy
    have hxbound : ‖x‖ ≤ r + 1 := by
      have ht := norm_le_insert y x
      rw [← dist_eq_norm, dist_comm] at ht
      linarith
    change Plane.supDist x 0 ≤ r + 1
    rw [Plane.supDist_zero]
    exact (Plane.supNorm_le_norm x).trans hxbound
  let A := Plane.mk (r + 2) 0
  have hAfar : A ∈ Plane.beyondSquare (r + 1) := by
    left
    change r + 1 < |r + 2|
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hA : A ∈ standardOutside p := by
    apply beyondSquare_subset_standardOutside p hPbound
    left
    change r < |r + 2|
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hAq : ∀ᶠ i in hyperfilter ℕ, A ∈ outside (q i).2.carrier :=
    hQbound.mono fun _ hi ↦ beyondSquare_subset_outside hi hAfar
  exact ⟨q, hq, hshadow, fun B hB ↦
    mem_deep_outer_of_near_boundary p hmax hs q hnear hA hB hAq⟩

end Reeken.NSA
