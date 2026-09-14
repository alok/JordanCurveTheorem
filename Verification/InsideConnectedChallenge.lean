import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Connected.PathConnected

open Set

namespace Verification

/-- The circle complement has a bounded path-connected region with the curve
as its boundary. The outside connectivity and inside simple connectivity are
separate conclusions and are not asserted by this milestone. -/
theorem curve_inside_connected
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      U.Nonempty ∧ V.Nonempty ∧ IsPathConnected U ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (range r)ᶜ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ‖x‖ ≤ R) ∧
      (∀ R : ℝ, ∃ x ∈ V, R < ‖x‖) ∧
      frontier U = range r ∧ frontier V = range r := by
  sorry

end Verification
