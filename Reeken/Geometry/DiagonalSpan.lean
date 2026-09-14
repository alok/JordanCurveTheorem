import Reeken.Geometry.PrePolygonDiagonal

/-! # The number of edges spanned by a diagonal

Ordering two cyclic indices by their natural representatives gives a proper
interval with at least two and at most all-but-two boundary edges.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem diagonal_gap_bounds {m : ℕ} {i j : ZMod (m + 3)}
    (hij : i.val < j.val) (hne : j ≠ i + 1) (hnprev : j ≠ i - 1) :
    2 ≤ j.val - i.val ∧ j.val - i.val ≤ m + 1 := by
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have he : j.val ≠ i.val + 1 := by
    intro he
    apply hne
    rw [← ZMod.natCast_rightInverse j, he, Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse i]
  have hends : ¬ (i.val = 0 ∧ j.val = m + 2) := by
    rintro ⟨hi0, hjlast⟩
    apply hnprev
    have hi' : i = 0 := (ZMod.val_eq_zero i).mp hi0
    have hfull : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    have hj' : j = ((m + 2 : ℕ) : ZMod (m + 3)) := by
      rw [← hjlast, ZMod.natCast_rightInverse]
    rw [hi', hj']
    push_cast at hfull ⊢
    linear_combination hfull
  omega

theorem exists_ordered_internal_diagonal {m : ℕ} (P : PrePolygon m) (hm : 0 < m) :
    ∃ (p q : ℕ), q < m + 3 ∧ 2 ≤ q - p ∧ q - p ≤ m + 1 ∧
      openSegment ℝ (P.vertex (p : ZMod (m + 3))) (P.vertex (q : ZMod (m + 3))) ⊆ inside P.carrier := by
  obtain ⟨i, j, hji, hjnext, hjprev, hseg⟩ := exists_internal_diagonal_prePolygon P hm
  have hne : i.val ≠ j.val := fun he ↦ hji (ZMod.val_injective _ he).symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨hlo, hhi⟩ := diagonal_gap_bounds hlt hjnext hjprev
    refine ⟨i.val, j.val, ZMod.val_lt j, hlo, hhi, ?_⟩
    rw [ZMod.natCast_rightInverse i, ZMod.natCast_rightInverse j]
    exact hseg
  · have hseg' : openSegment ℝ (P.vertex j) (P.vertex i) ⊆ inside P.carrier := by
      rwa [openSegment_symm]
    obtain ⟨-, hnext, hprev⟩ := nonadjacent_of_openSegment_inside P hseg'
    obtain ⟨hlo, hhi⟩ := diagonal_gap_bounds hlt hnext hprev
    refine ⟨j.val, i.val, ZMod.val_lt i, hlo, hhi, ?_⟩
    rw [ZMod.natCast_rightInverse j, ZMod.natCast_rightInverse i]
    exact hseg'

end Reeken.Geometry
