import Reeken.Geometry.SpokeConnectivity
import Reeken.Geometry.LoopPuncture

/-! # Two boundary curves joined by disjoint connections

Two disjoint bridges ensure that deleting one point leaves at least one complete
bridge. All remaining pieces of other bridges can reach one of their endpoints.
This supplies the connectivity hypothesis for the finite ring drawing in Lemma 3.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPreconnected_union_bridge {C D : Set E} {a b : E}
    (hC : IsPreconnected C) (hD : IsPreconnected D) (ha : a ∈ C) (hb : b ∈ D) :
    IsPreconnected ((C ∪ D) ∪ segment ℝ a b) := by
  have h := (hC.union a ha (left_mem_segment ℝ _ _) (convex_segment a b).isPreconnected).union
    b (Or.inr (right_mem_segment ℝ a b)) hb hD
  rwa [union_right_comm] at h

theorem isPreconnected_union_bridges {ι : Type*} [Nonempty ι] {C D : Set E}
    {a b : ι → E} (hC : IsConnected C) (hD : IsPreconnected D)
    (ha : ∀ j, a j ∈ C) (hb : ∀ j, b j ∈ D) :
    IsPreconnected ((C ∪ D) ∪ ⋃ j, segment ℝ (a j) (b j)) := by
  obtain ⟨w, hw⟩ := hC.nonempty
  have hcommon : (⋂ j, (C ∪ D) ∪ segment ℝ (a j) (b j)).Nonempty :=
    ⟨w, mem_iInter.mpr fun _ ↦ Or.inl (Or.inl hw)⟩
  have h := isPreconnected_iUnion hcommon (fun j ↦
    isPreconnected_union_bridge hC.isPreconnected hD (ha j) (hb j))
  simpa only [← union_iUnion] using h

theorem isPreconnected_punctured_union_bridges {ι : Type*} [Nonempty ι] {C D : Set E}
    {a b : ι → E} {z : E} (hC : IsPreconnected (C \ {z}))
    (hD : IsPreconnected (D \ {z})) (ha : ∀ j, a j ∈ C) (hb : ∀ j, b j ∈ D)
    (hbridge : ∃ j, z ∉ segment ℝ (a j) (b j)) :
    IsPreconnected (((C ∪ D) ∪ ⋃ j, segment ℝ (a j) (b j)) \ {z}) := by
  obtain ⟨k, hk⟩ := hbridge
  have hak : a k ≠ z := fun he ↦ hk (he ▸ left_mem_segment ℝ _ _)
  have hbk : b k ≠ z := fun he ↦ hk (he ▸ right_mem_segment ℝ _ _)
  let base := (C ∪ D) ∪ segment ℝ (a k) (b k)
  have hbase : IsPreconnected (base \ {z}) := by
    have h := isPreconnected_union_bridge hC hD ⟨ha k, hak⟩ ⟨hb k, hbk⟩
    change IsPreconnected (((C ∪ D) ∪ segment ℝ (a k) (b k)) \ {z})
    simpa only [union_sdiff_distrib, sdiff_singleton_eq_self hk] using h
  have hne : (base \ {z}).Nonempty := ⟨a k, Or.inl (Or.inl (ha k)), hak⟩
  have h := isPreconnected_punctured_union_segments hbase hne
    (fun j ↦ Or.inl (Or.inl (ha j))) (fun j ↦ Or.inl (Or.inr (hb j)))
  have heq : base ∪ ⋃ j, segment ℝ (a j) (b j) = (C ∪ D) ∪ ⋃ j, segment ℝ (a j) (b j) := by
    change ((C ∪ D) ∪ segment ℝ (a k) (b k)) ∪ _ = _
    rw [union_assoc, union_eq_right.mpr (subset_iUnion (fun j ↦ segment ℝ (a j) (b j)) k)]
  rwa [heq] at h

/-- In particular, two disjoint connections suffice at every puncture. -/
theorem isPreconnected_punctured_two_curves_bridges {ι : Type*} [Nonempty ι]
    {C D : Set Plane} {a b : ι → Plane} (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (ha : ∀ j, a j ∈ C) (hb : ∀ j, b j ∈ D) {j k : ι}
    (hdis : Disjoint (segment ℝ (a j) (b j)) (segment ℝ (a k) (b k))) (z : Plane) :
    IsPreconnected (((C ∪ D) ∪ ⋃ j, segment ℝ (a j) (b j)) \ {z}) := by
  apply isPreconnected_punctured_union_bridges (isPreconnected_punctured_jordan hC z)
    (isPreconnected_punctured_jordan hD z) ha hb
  by_cases hz : z ∈ segment ℝ (a j) (b j)
  · exact ⟨k, fun hz' ↦ Set.disjoint_left.mp hdis hz hz'⟩
  · exact ⟨j, hz⟩

end Reeken.Geometry
