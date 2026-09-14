import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.ZMod.Basic

open Set

namespace Verification

/-- Finite polygonal separation, independently stated with explicit cyclic segments.
Collinear consecutive edges are allowed, but distinct edges can only meet at endpoints. -/
theorem finite_polygon_separation (m : ℕ)
    (v : ZMod (m + 3) → EuclideanSpace ℝ (Fin 2))
    (hi : Function.Injective v)
    (he : ∀ i j, i ≠ j →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆ {v i, v (i + 1)}) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
      U ∪ V = (⋃ i, segment ℝ (v i) (v (i + 1)))ᶜ ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = ⋃ i, segment ℝ (v i) (v (i + 1)) ∧
      frontier V = ⋃ i, segment ℝ (v i) (v (i + 1)) := by
  sorry

end Verification
