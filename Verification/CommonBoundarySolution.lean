import Reeken.Nonstandard.CommonBoundary
import Reeken.Nonstandard.RegionBounds
import Reeken.Geometry.CircleParametrization

open Set Reeken.Geometry Reeken.NSA

namespace Verification

/-- The published common-boundary conclusion for every continuous circle embedding. -/
theorem curve_common_boundary
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      U.Nonempty ∧ V.Nonempty ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (range r)ᶜ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ‖x‖ ≤ R) ∧
      (∀ R : ℝ, ∃ x ∈ V, R < ‖x‖) ∧
      frontier U = range r ∧ frontier V = range r := by
  let f := SimpleLoop.ofPlaneCircle r hcont hinj
  have himage : f '' Icc 0 1 = range r := SimpleLoop.ofPlaneCircle_image r hcont hinj
  obtain ⟨p, hmax, hs, _⟩ := exists_simple_polygon f
  refine ⟨standardInside p, standardOutside p, standardInside_nonempty p hmax hs,
    standardOutside_nonempty p, isOpen_standardInside p, isOpen_standardOutside p,
    disjoint_standardRegions p, ?_, exists_standardInside_radius p,
    exists_standardOutside_beyond p, ?_, ?_⟩
  · rw [standardRegions_union p hmax hs, himage]
  · rw [frontier_standardInside p hmax hs, himage]
  · rw [frontier_standardOutside p hmax hs, himage]

end Verification
