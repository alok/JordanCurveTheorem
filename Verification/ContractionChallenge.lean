import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set

namespace Verification

/-- The closed bounded region of a nondegenerate triangle contracts, and its
open bounded region is simply connected. The statement uses explicit segments. -/
theorem triangle_contraction (a b c : EuclideanSpace ℝ (Fin 2))
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    let C := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
    let U := {x | x ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ x)}
    ContractibleSpace (closure U) ∧ IsSimplyConnected U := by
  sorry

/-- A closed convex piece attached along a segment preserves contractibility. -/
theorem convex_attachment_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E) (hA : IsClosed A) (hB : IsClosed B) (hconv : Convex ℝ A)
    (a b : E) (hinter : A ∩ B = segment ℝ a b) [ContractibleSpace B] :
    ContractibleSpace (A ∪ B : Set E) := by
  sorry

end Verification
