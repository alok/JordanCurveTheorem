import Reeken.Geometry.InscribedPolygon

/-! # Cyclic adjacency of polygon indices -/

namespace Reeken.Geometry

theorem nextIndex_val {n : ℕ} (i : Fin (n + 1)) :
    (nextIndex n i).val = if i.val = n then 0 else i.val + 1 := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Nat.ne_of_lt i.isLt]

theorem nextIndex_ne_self {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    nextIndex n i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [nextIndex_val] at hv
  split_ifs at hv <;> omega

/-- Distinct vertices that are not consecutive in either cyclic direction. -/
def Nonadjacent {n : ℕ} (a b : Fin (n + 1)) : Prop :=
  a ≠ b ∧ nextIndex n a ≠ b ∧ nextIndex n b ≠ a

theorem Nonadjacent.symm {n : ℕ} {a b : Fin (n + 1)} (h : Nonadjacent a b) :
    Nonadjacent b a := ⟨Ne.symm h.1, h.2.2, h.2.1⟩

theorem Nonadjacent.ordered {n : ℕ} {a b : Fin (n + 1)}
    (h : Nonadjacent a b) (hab : a < b) :
    a.val + 1 < b.val ∧ (0 < a.val ∨ b.val < n) := by
  have ha := a.isLt
  have hb := b.isLt
  have h₁ : (if a.val = n then 0 else a.val + 1) ≠ b.val := by
    rw [← nextIndex_val]
    exact fun he ↦ h.2.1 (Fin.ext he)
  have h₂ : (if b.val = n then 0 else b.val + 1) ≠ a.val := by
    rw [← nextIndex_val]
    exact fun he ↦ h.2.2 (Fin.ext he)
  split_ifs at h₁ h₂ <;> omega

theorem nonadjacent_next_next {n : ℕ} (hn : 3 ≤ n) (i : Fin (n + 1)) :
    Nonadjacent i (nextIndex n (nextIndex n i)) := by
  have hi := i.isLt
  have hnext := (nextIndex n i).isLt
  have hnext₂ := (nextIndex n (nextIndex n i)).isLt
  have h₁ := nextIndex_val i
  have h₂ := nextIndex_val (nextIndex n i)
  have h₃ := nextIndex_val (nextIndex n (nextIndex n i))
  constructor
  · intro he
    have := congrArg Fin.val he
    split_ifs at h₁ h₂ h₃ <;> omega
  constructor
  · intro he
    have := congrArg Fin.val he
    split_ifs at h₁ h₂ h₃ <;> omega
  · intro he
    have := congrArg Fin.val he
    split_ifs at h₁ h₂ h₃ <;> omega

end Reeken.Geometry
