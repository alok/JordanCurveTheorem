import Reeken.Geometry.Equidistant
import Reeken.Nonstandard.CompactSeparation

/-! # The appreciable equal-distance estimate in Section 3 -/

open Filter Set Metric

namespace Reeken.NSA

variable {E : Type*} [MetricSpace E] [Nonempty E]

/-- Equal distances to the two arcs cannot be infinitesimal on a compact set avoiding their
common shadow. The bound applies to every point of the full polygon, the union of the arcs. -/
theorem equidistant_uniform_bound {K : Set E} (hK : IsCompact K) {s t : ℕ → Set E}
    (hdis : Disjoint K (shadow s ∩ shadow t))
    (hcompact : ∀ᶠ i in hyperfilter ℕ,
      IsCompact (s i) ∧ (s i).Nonempty ∧ IsCompact (t i) ∧ (t i).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ K,
      infDist x (s i) = infDist x (t i) → ∀ y ∈ s i ∪ t i, δ ≤ dist y x := by
  obtain ⟨δ, hδ, hd⟩ := compact_separation_from_common_shadow hK hdis
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hd, hcompact] with i hi hc
  intro x hx he
  obtain ⟨a, ha, hda⟩ := hc.1.exists_infDist_eq_dist hc.2.1 x
  obtain ⟨b, hb, hdb⟩ := hc.2.2.1.exists_infDist_eq_dist hc.2.2.2 x
  have hbound := hi x hx a ha b hb
  rw [dist_comm a x, dist_comm b x, ← hda, ← hdb, ← he, max_self] at hbound
  intro y hy
  rw [dist_comm]
  rcases hy with hy | hy
  · exact hbound.trans (infDist_le_dist_of_mem hy)
  · rw [he] at hbound
    exact hbound.trans (infDist_le_dist_of_mem hy)

end Reeken.NSA
