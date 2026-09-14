import Reeken.Nonstandard.Equidistant
import Reeken.Nonstandard.DeepStandardPart

/-! # Reduction of Section 3 to the finite boundary-connector construction

The connector hypotheses below are explicit geometric obligations, not yet an
instantiated theorem about the clipped polygon. Once such connectors are constructed,
the equal-distance and standard-part steps are proved here.
-/

open Filter Set Metric

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact family of connectors crossing the two arcs supplies a standard deep point,
provided the connector is on the chosen side away from its endpoints. -/
theorem exists_deep_point_of_connectors {K : Set E} (hK : IsCompact K)
    {s t c u v : ℕ → Set E} (hdis : Disjoint K (shadow s ∩ shadow t))
    (hcompact : ∀ᶠ i in hyperfilter ℕ,
      IsCompact (s i) ∧ (s i).Nonempty ∧ IsCompact (t i) ∧ (t i).Nonempty)
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (s i ∪ t i)ᶜ)
    (hc : ∀ᶠ i in hyperfilter ℕ, IsPreconnected (c i) ∧ c i ⊆ K ∧
      (c i ∩ s i).Nonempty ∧ (c i ∩ t i).Nonempty ∧ c i \ (s i ∪ t i) ⊆ u i) :
    (K ∩ deep u).Nonempty := by
  obtain ⟨δ, hδ, hd⟩ := equidistant_uniform_bound hK hdis hcompact
  have he : ∀ᶠ i in hyperfilter ℕ,
      ∃ x : E, x ∈ K ∧ x ∈ u i ∧ ∀ y ∈ s i ∪ t i, δ ≤ dist y x := by
    filter_upwards [hc, hd] with i hi hdi
    obtain ⟨x, hx, heq⟩ := Reeken.Geometry.exists_equidistant hi.1 hi.2.2.1 hi.2.2.2.1
    have hxK := hi.2.1 hx
    have hbound := hdi x hxK heq
    have hnot : x ∉ s i ∪ t i := by
      intro hmem
      have h := hbound x hmem
      simp only [dist_self, not_le_of_gt hδ] at h
    exact ⟨x, hxK, hi.2.2.2.2 ⟨hx, hnot⟩, hbound⟩
  obtain ⟨x, hx⟩ := (exists_holds (U := hyperfilter ℕ)
    (fun i x ↦ x ∈ K ∧ x ∈ u i ∧ ∀ y ∈ s i ∪ t i, δ ≤ dist y x)).mpr he
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  obtain ⟨a, ha, hxa⟩ := compact_standard_part hK (x := ofSeq (U := hyperfilter ℕ) x) (hx.mono fun i hi ↦ hi.1)
  exact ⟨a, ha, standard_part_mem_deep hsep (hx.mono fun i hi ↦ hi.2.1) hδ
    (hx.mono fun i hi ↦ hi.2.2) hxa⟩

end Reeken.NSA
