import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! # Extracting the boundary interval between the two polygon arcs

Along a path avoiding the arcs' common endpoints, take the first contact with the
second arc and then the last contact with the first. The intervening subpath lies
on the remaining closed part of the cell boundary.
-/

open Set

namespace Reeken.Geometry

variable {E : Type*} [TopologicalSpace E]

/-- A path covered by two disjoint closed pieces and a third closed piece contains a
subpath in the third piece connecting the first two, with its interior avoiding both. -/
theorem exists_boundary_subpath {f : ℝ → E} (hf : Continuous f) {A B S : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hS : IsClosed S)
    (h0 : f 0 ∈ A) (h1 : f 1 ∈ B)
    (hdis : Disjoint (f '' Icc 0 1) (A ∩ B))
    (hcover : f '' Icc 0 1 ⊆ (A ∪ B) ∪ S) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ f a ∈ A ∧ f b ∈ B ∧
      f '' Icc a b ⊆ S ∧ f '' Ioo a b ⊆ (A ∪ B)ᶜ := by
  have hKB : IsCompact (Icc (0 : ℝ) 1 ∩ f ⁻¹' B) :=
    isCompact_Icc.inter_right (hB.preimage hf)
  obtain ⟨b, hb, hmin⟩ := hKB.exists_isMinOn ⟨1, ⟨by norm_num, h1⟩⟩ continuous_id.continuousOn
  have hKA : IsCompact (Icc 0 b ∩ f ⁻¹' A) :=
    isCompact_Icc.inter_right (hA.preimage hf)
  obtain ⟨a, ha, hmax⟩ := hKA.exists_isMaxOn ⟨0, ⟨⟨le_rfl, hb.1.1⟩, h0⟩⟩
    continuous_id.continuousOn
  have hab : a < b := by
    apply lt_of_le_of_ne ha.1.2
    intro he
    exact Set.disjoint_left.mp hdis ⟨b, hb.1, rfl⟩ ⟨he ▸ ha.2, hb.2⟩
  have hav : f '' Ioo a b ⊆ (A ∪ B)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ (htA | htB)
    · exact (not_le_of_gt ht.1) (hmax ⟨⟨ha.1.1.trans ht.1.le, ht.2.le⟩, htA⟩)
    · exact (not_le_of_gt ht.2) (hmin ⟨⟨ha.1.1.trans ht.1.le, ht.2.le.trans hb.1.2⟩, htB⟩)
  have hmid : f '' Ioo a b ⊆ S := by
    intro x hx
    have hx01 : x ∈ f '' Icc 0 1 := by
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨t, ⟨ha.1.1.trans ht.1.le, ht.2.le.trans hb.1.2⟩, rfl⟩
    exact (hcover hx01).resolve_left (hav hx)
  have hwhole : f '' Icc a b ⊆ S := by
    rw [← closure_Ioo hab.ne]
    exact (image_closure_subset_closure_image hf).trans (closure_minimal hmid hS)
  exact ⟨a, b, ha.1.1, hab, hb.1.2, ha.2, hb.2, hwhole, hav⟩

end Reeken.Geometry
