import Reeken.Geometry.InscribedPolygon

/-! # The two arcs determined by two ordered vertices -/

open Set Metric

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} (p : InscribedPolygon f)

def forwardArc (a b : Fin (p.n + 1)) : Set E :=
  {x | x = p.vertex a ∨ ∃ i, a ≤ i ∧ i < b ∧
    x ∈ segment ℝ (p.vertex i) (p.vertex (nextIndex p.n i))}

def backwardArc (a b : Fin (p.n + 1)) : Set E :=
  {x | x = p.vertex b ∨ ∃ i, (i < a ∨ b ≤ i) ∧
    x ∈ segment ℝ (p.vertex i) (p.vertex (nextIndex p.n i))}

theorem arcs_union (a b : Fin (p.n + 1)) : p.forwardArc a b ∪ p.backwardArc a b = p.trace := by
  ext x
  constructor
  · rintro (hx | hx)
    · rcases hx with rfl | ⟨i, _, _, hx⟩
      · exact mem_iUnion.mpr ⟨a, left_mem_segment ℝ _ _⟩
      · exact mem_iUnion.mpr ⟨i, hx⟩
    · rcases hx with rfl | ⟨i, _, hx⟩
      · exact mem_iUnion.mpr ⟨b, left_mem_segment ℝ _ _⟩
      · exact mem_iUnion.mpr ⟨i, hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hia : i < a
    · exact Or.inr (Or.inr ⟨i, Or.inl hia, hi⟩)
    · by_cases hbi : b ≤ i
      · exact Or.inr (Or.inr ⟨i, Or.inr hbi, hi⟩)
      · exact Or.inl (Or.inr ⟨i, le_of_not_gt hia, lt_of_not_ge hbi, hi⟩)

/-- The forward arc stays in any ball containing its vertices. -/
theorem forwardArc_subset_ball {a b : Fin (p.n + 1)} (hab : a ≤ b) {c : E} {ε : ℝ}
    (hv : ∀ j, a ≤ j → j ≤ b → p.vertex j ∈ ball c ε) :
    p.forwardArc a b ⊆ ball c ε := by
  rintro x (rfl | ⟨i, hai, hib, hx⟩)
  · exact hv a le_rfl hab
  · have hin : i ≠ Fin.last p.n := ne_of_lt (hib.trans_le (Fin.le_last b))
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hin
    rw [nextIndex_castSucc] at hx
    have hk : k.succ ≤ b := Nat.succ_le_of_lt hib
    exact (convex_ball c ε).segment_subset (hv _ hai hib.le)
      (hv _ (hai.trans (Fin.castSucc_le_succ k)) hk) hx

/-- The complementary arc stays in any ball containing its vertices, including the wrap edge. -/
theorem backwardArc_subset_ball {a b : Fin (p.n + 1)} {c : E} {ε : ℝ}
    (hv : ∀ j, j ≤ a ∨ b ≤ j → p.vertex j ∈ ball c ε) :
    p.backwardArc a b ⊆ ball c ε := by
  rintro x (rfl | ⟨i, hi, hx⟩)
  · exact hv b (Or.inr le_rfl)
  · have hvi : p.vertex i ∈ ball c ε := hv i (hi.imp (fun h ↦ h.le) id)
    have hvn : p.vertex (nextIndex p.n i) ∈ ball c ε := by
      by_cases hilast : i = Fin.last p.n
      · rw [hilast, nextIndex_last]
        exact hv 0 (Or.inl (Fin.zero_le a))
      · obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
        rw [nextIndex_castSucc]
        apply hv
        rcases hi with hi | hi
        · exact Or.inl (show k.succ ≤ a from Nat.succ_le_of_lt hi)
        · exact Or.inr (hi.trans (Fin.castSucc_le_succ k))
    exact (convex_ball c ε).segment_subset hvi hvn hx

end Reeken.Geometry.InscribedPolygon
