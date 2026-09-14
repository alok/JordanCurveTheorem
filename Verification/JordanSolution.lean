import Reeken.Jordan

namespace Verification

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
  exact Reeken.jordanCurveTheorem r hcont hinj

end Verification
