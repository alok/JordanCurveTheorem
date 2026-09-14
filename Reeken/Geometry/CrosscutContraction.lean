import Reeken.Geometry.ConvexAttachment
import Reeken.Geometry.TriangleContraction
import Schoenflies.Realization

/-! # Contraction across a polygonal crosscut

The finite crosscut theorem identifies two open cells. Their closed interiors
cover the parent's closed interior and meet exactly on the crosscut. Splitting
off a triangle therefore reduces contractibility to the remaining polygon.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁}
  {J₂ : ClosedPolygon m₂} {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

theorem closed_inside_union_of_crosscut
    (h : IsPolygonalCrosscut C J₁ J₂ K a k y) (hy : y ∈ outside C.carrier) :
    closure (inside J₁.carrier) ∪ closure (inside J₂.carrier) =
      closure (inside C.carrier) := by
  have hsub₁ : inside J₁.carrier ⊆ inside C.carrier := by
    have hs := h.cell_subset₁
    rw [h.cell₁_eq_inside hy, C.isSeparating_carrier.farRegion_eq_inside hy] at hs
    exact hs.trans sdiff_subset
  have hsub₂ : inside J₂.carrier ⊆ inside C.carrier := by
    have hs := h.cell_subset₂
    rw [h.cell₂_eq_inside hy, C.isSeparating_carrier.farRegion_eq_inside hy] at hs
    exact hs.trans sdiff_subset
  refine subset_antisymm (union_subset (closure_mono hsub₁) (closure_mono hsub₂)) ?_
  apply closure_minimal _ (isClosed_closure.union isClosed_closure)
  intro x hx
  by_cases hxK : x ∈ cover K
  · left
    exact frontier_subset_closure (J₁.isSeparating_carrier.frontier_inside.symm ▸
      h.cover_subset_carrier₁ hxK)
  · have he : x ∈ inside J₁.carrier ∪ inside J₂.carrier := h.inside_diff_eq hy ▸ ⟨hx, hxK⟩
    exact he.elim (fun h₁ ↦ Or.inl (subset_closure h₁)) (fun h₂ ↦ Or.inr (subset_closure h₂))

theorem closed_inside_inter_of_crosscut
    (h : IsPolygonalCrosscut C J₁ J₂ K a k y) (hy : y ∈ outside C.carrier)
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (hends : {C.vertex a, C.vertex (a + k)} ⊆ cover K) :
    closure (inside J₁.carrier) ∩ closure (inside J₂.carrier) = cover K := by
  have hd : Disjoint (inside J₁.carrier) (inside J₂.carrier) := by
    simpa only [h.cell₁_eq_inside hy, h.cell₂_eq_inside hy] using h.cells_disjoint
  refine subset_antisymm ?_ ?_
  · rintro x ⟨hx₁, hx₂⟩
    have hb₁ : x ∈ J₁.carrier := by
      have he := (IsRegionOf.inside J₁.carrier).closure_eq J₁.isSeparating_carrier
      have hx := he ▸ hx₁
      exact hx.resolve_left (fun hin ↦ disjoint_left.mp
        (hd.closure_right J₁.isSeparating_carrier.isOpen_inside) hin hx₂)
    have hb₂ : x ∈ J₂.carrier := by
      have he := (IsRegionOf.inside J₂.carrier).closure_eq J₂.isSeparating_carrier
      have hx := he ▸ hx₂
      exact hx.resolve_left (fun hin ↦ disjoint_left.mp
        (hd.closure_left J₂.isSeparating_carrier.isOpen_inside) hx₁ hin)
    rw [h.carrier₁] at hb₁
    rw [h.symm.carrier₁] at hb₂
    rcases hb₁ with ha₁ | hxK
    · rcases hb₂ with ha₂ | hxK
      · exact hends (C.arc_inter a hk1 hk2 ▸ ⟨ha₁, ha₂⟩)
      · exact hxK
    · exact hxK
  · intro x hx
    exact ⟨frontier_subset_closure (J₁.isSeparating_carrier.frontier_inside.symm ▸
        h.cover_subset_carrier₁ hx),
      frontier_subset_closure (J₂.isSeparating_carrier.frontier_inside.symm ▸
        h.symm.cover_subset_carrier₁ hx)⟩

/-- A diagonal cutting off a triangle permits the original polygon to contract
whenever the smaller polygon contracts. All crosscut conditions are geometric. -/
theorem contractible_closed_inside_of_triangle_crosscut {T : ClosedPolygon 0}
    (h : IsPolygonalCrosscut C T J₂ K a k y) (hy : y ∈ outside C.carrier)
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (hK : cover K = segment ℝ (C.vertex a) (C.vertex (a + k)))
    [ContractibleSpace (closure (inside J₂.carrier))] :
    ContractibleSpace (closure (inside C.carrier)) := by
  rw [← closed_inside_union_of_crosscut h hy]
  have hconv : Convex ℝ (closure (inside T.carrier)) := by
    rw [triangle_closed_inside_eq_hull T]
    exact convex_convexHull ℝ _
  apply contractibleSpace_union_of_segment_inter isClosed_closure isClosed_closure hconv
    (C.vertex a) (C.vertex (a + k))
  rw [closed_inside_inter_of_crosscut h hy hk1 hk2, hK]
  rw [hK]
  exact pair_subset (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)

end Reeken.Geometry
