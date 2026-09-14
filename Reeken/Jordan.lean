import Reeken.Nonstandard.SimplyConnected
import Reeken.Nonstandard.OutsideConnectivity
import Reeken.Nonstandard.CommonBoundary
import Reeken.Nonstandard.RegionBounds
import Reeken.Geometry.CircleParametrization

/-! # The Kanovei–Reeken Jordan curve theorem

For every continuous injective circle map, the complement has a bounded simply
connected inside and an unbounded outside, both open and path connected, with the
curve as their common boundary. The proof uses the developed nonstandard polygon
approximation and standard-region machinery.
-/

open Set Reeken.Geometry Reeken.NSA

namespace Reeken

theorem jordanCurveTheorem
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      inside.Nonempty ∧ outside.Nonempty ∧
      IsOpen inside ∧ IsOpen outside ∧ Disjoint inside outside ∧
      inside ∪ outside = (Set.range r)ᶜ ∧
      IsPathConnected inside ∧ IsPathConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      frontier inside = Set.range r ∧ frontier outside = Set.range r ∧
      IsSimplyConnected inside := by
  let f := SimpleLoop.ofPlaneCircle r hcont hinj
  have himage : f '' Icc 0 1 = range r := SimpleLoop.ofPlaneCircle_image r hcont hinj
  obtain ⟨p, hmax, hs, _⟩ := exists_simple_polygon f
  refine ⟨standardInside p, standardOutside p, standardInside_nonempty p hmax hs,
    standardOutside_nonempty p, isOpen_standardInside p, isOpen_standardOutside p,
    disjoint_standardRegions p, ?_, isPathConnected_standardInside p hmax hs,
    isPathConnected_standardOutside p hmax hs, isBounded_standardInside p,
    not_isBounded_standardOutside p, ?_, ?_, isSimplyConnected_standardInside p hmax hs⟩
  · rw [standardRegions_union p hmax hs, himage]
  · rw [frontier_standardInside p hmax hs, himage]
  · rw [frontier_standardOutside p hmax hs, himage]

end Reeken
