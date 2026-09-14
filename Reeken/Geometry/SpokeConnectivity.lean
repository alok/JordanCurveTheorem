import Reeken.Geometry.Segments
import Mathlib.Analysis.Convex.PathConnected

/-! # Adding boundary connections preserves punctured connectivity

A segment attached at both endpoints to a set cannot disconnect it after one
point is removed. Every surviving point of the segment can still reach at least
one of the two attached endpoints without passing through the deleted point.
-/

open Set

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem segment_endpoint_access_avoiding_point {a b x z : E}
    (hx : x ∈ segment ℝ a b) (hxz : x ≠ z) :
    z ∉ segment ℝ a x ∨ z ∉ segment ℝ b x := by
  by_contra h
  push Not at h
  have ha := dist_add_dist_of_mem_segment h.1
  have hb := dist_add_dist_of_mem_segment h.2
  have hab := dist_add_dist_of_mem_segment hx
  have ht := dist_triangle a z b
  rw [dist_comm b z, dist_comm b x] at hb
  have hpos : 0 < dist z x := dist_pos.mpr (Ne.symm hxz)
  linarith

theorem isPreconnected_punctured_union_segment {C : Set E} {a b z : E}
    (hC : IsPreconnected (C \ {z})) (hne : (C \ {z}).Nonempty)
    (ha : a ∈ C) (hb : b ∈ C) :
    IsPreconnected ((C ∪ segment ℝ a b) \ {z}) := by
  obtain ⟨w, hwC, hwz⟩ := hne
  apply isPreconnected_of_forall w
  rintro x ⟨hxC | hxseg, hxz⟩
  · exact ⟨C \ {z}, fun y hy ↦ ⟨Or.inl hy.1, hy.2⟩,
      ⟨hwC, hwz⟩, ⟨hxC, hxz⟩, hC⟩
  · have hattach : ∀ e ∈ C, e ∈ segment ℝ a b → z ∉ segment ℝ e x →
        ∃ T, T ⊆ (C ∪ segment ℝ a b) \ {z} ∧ w ∈ T ∧ x ∈ T ∧ IsPreconnected T := by
      intro e heC heseg havoid
      have hez : e ≠ z := fun he ↦ havoid (he ▸ left_mem_segment ℝ e x)
      have hsegsub := (convex_segment a b).segment_subset heseg hxseg
      refine ⟨(C \ {z}) ∪ segment ℝ e x, ?_, Or.inl ⟨hwC, hwz⟩,
        Or.inr (right_mem_segment ℝ e x), ?_⟩
      · rintro y (hy | hy)
        · exact ⟨Or.inl hy.1, hy.2⟩
        · exact ⟨Or.inr (hsegsub hy), fun he ↦ havoid (he ▸ hy)⟩
      · exact hC.union e ⟨heC, hez⟩ (left_mem_segment ℝ e x) (convex_segment e x).isPreconnected
    rcases segment_endpoint_access_avoiding_point hxseg hxz with h | h
    · exact hattach a ha (left_mem_segment ℝ a b) h
    · exact hattach b hb (right_mem_segment ℝ a b) h

/-- A whole indexed family of doubly attached segments preserves the same property. -/
theorem isPreconnected_punctured_union_segments {ι : Type*} [Nonempty ι]
    {C : Set E} {a b : ι → E} {z : E} (hC : IsPreconnected (C \ {z}))
    (hne : (C \ {z}).Nonempty) (ha : ∀ i, a i ∈ C) (hb : ∀ i, b i ∈ C) :
    IsPreconnected ((C ∪ ⋃ i, segment ℝ (a i) (b i)) \ {z}) := by
  have hpieces : ∀ i, IsPreconnected ((C ∪ segment ℝ (a i) (b i)) \ {z}) :=
    fun i ↦ isPreconnected_punctured_union_segment hC hne (ha i) (hb i)
  obtain ⟨w, hwC, hwz⟩ := hne
  have hcommon : (⋂ i, (C ∪ segment ℝ (a i) (b i)) \ {z}).Nonempty :=
    ⟨w, mem_iInter.mpr fun _ ↦ ⟨Or.inl hwC, hwz⟩⟩
  simpa only [← iUnion_sdiff, ← union_iUnion] using isPreconnected_iUnion hcommon hpieces

end Reeken.Geometry
