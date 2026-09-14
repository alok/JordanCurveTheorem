import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue

/-! # The equal-distance point in the common-boundary argument -/

open Set Metric

namespace Reeken.Geometry

variable {E : Type*} [MetricSpace E]

/-- A connected set meeting both sets contains a point equidistant from them. -/
theorem exists_equidistant {s A B : Set E} (hs : IsPreconnected s)
    (ha : (s ∩ A).Nonempty) (hb : (s ∩ B).Nonempty) :
    ∃ x ∈ s, infDist x A = infDist x B := by
  obtain ⟨a, has, haA⟩ := ha
  obtain ⟨b, hbs, hbB⟩ := hb
  apply hs.intermediate_value₂ has hbs
    (continuous_infDist_pt A).continuousOn (continuous_infDist_pt B).continuousOn
  · rw [infDist_zero_of_mem haA]
    exact infDist_nonneg
  · rw [infDist_zero_of_mem hbB]
    exact infDist_nonneg

/-- If the connector avoids the common endpoints, its balanced point is off both arcs. -/
theorem exists_equidistant_pos {s A B : Set E} (hs : IsPreconnected s)
    (hA : IsClosed A) (hB : IsClosed B)
    (ha : (s ∩ A).Nonempty) (hb : (s ∩ B).Nonempty)
    (hdis : Disjoint s (A ∩ B)) :
    ∃ x ∈ s, 0 < infDist x A ∧ infDist x A = infDist x B := by
  obtain ⟨x, hx, he⟩ := exists_equidistant hs ha hb
  refine ⟨x, hx, ?_, he⟩
  apply lt_of_le_of_ne infDist_nonneg
  intro hz
  have hxA : x ∈ A := (hA.mem_iff_infDist_zero (ha.mono inter_subset_right)).mpr hz.symm
  have hxB : x ∈ B := (hB.mem_iff_infDist_zero (hb.mono inter_subset_right)).mpr (he ▸ hz.symm)
  exact Set.disjoint_left.mp hdis hx ⟨hxA, hxB⟩

end Reeken.Geometry
