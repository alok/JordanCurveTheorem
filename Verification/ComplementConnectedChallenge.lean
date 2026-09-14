import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Connected.PathConnected

open Set

namespace Verification

/-- The Jordan separation and common-boundary conclusion for every continuous
circle embedding. Simple connectivity is a separate, still-open conclusion. -/
theorem curve_complement_connected
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      U.Nonempty ∧ V.Nonempty ∧ IsPathConnected U ∧ IsPathConnected V ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (range r)ᶜ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ‖x‖ ≤ R) ∧
      (∀ R : ℝ, ∃ x ∈ V, R < ‖x‖) ∧
      frontier U = range r ∧ frontier V = range r := by
  sorry

end Verification
