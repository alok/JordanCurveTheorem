import Reeken.Geometry.PolygonSlice

/-! # Deleting an interval of vertices and retaining the outer arc -/

namespace Reeken.Geometry

/-- Delete `d` vertices immediately after position `a`. -/
def skipIndex (n a d : ℕ) (h : a + d + 1 ≤ n) (i : Fin (n - d + 1)) : Fin (n + 1) :=
  ⟨if i.val ≤ a then i.val else i.val + d, by
    have := i.isLt
    split_ifs <;> omega⟩

@[simp] theorem skipIndex_zero (n a d : ℕ) (h : a + d + 1 ≤ n) :
    skipIndex n a d h 0 = 0 := by ext; simp [skipIndex]

@[simp] theorem skipIndex_last (n a d : ℕ) (h : a + d + 1 ≤ n) :
    skipIndex n a d h (Fin.last (n - d)) = Fin.last n := by
  ext
  simp only [skipIndex, Fin.val_last]
  split_ifs <;> omega

theorem skipIndex_strictMono (n a d : ℕ) (h : a + d + 1 ≤ n) :
    StrictMono (skipIndex n a d h) := by
  intro i j hij
  change (if i.val ≤ a then i.val else i.val + d) <
    (if j.val ≤ a then j.val else j.val + d)
  split_ifs <;> omega

theorem skipIndex_consecutive (n a d : ℕ) (h : a + d + 1 ≤ n)
    (i : Fin (n - d)) (hi : i.val ≠ a) :
    ∃ k : Fin n, skipIndex n a d h i.castSucc = k.castSucc ∧
      skipIndex n a d h i.succ = k.succ := by
  have hv : (skipIndex n a d h i.succ).val = (skipIndex n a d h i.castSucc).val + 1 := by
    simp only [skipIndex, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega
  let k : Fin n := ⟨(skipIndex n a d h i.castSucc).val, by
    have := (skipIndex n a d h i.succ).isLt
    omega⟩
  exact ⟨k, rfl, Fin.ext hv⟩

namespace InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E}
variable (p : InscribedPolygon f) (a d : ℕ) (h : a + d + 1 ≤ p.n)

/-- Retain the outer arc, replacing the deleted interval by one shortcut. -/
def deleteBetween
    (hgap : p.time ⟨a + d + 1, by omega⟩ - p.time ⟨a, by omega⟩ ≤ 1 / 2) :
    InscribedPolygon f where
  n := p.n - d
  time i := p.time (skipIndex p.n a d h i)
  time_mem i := p.time_mem _
  increasing := p.increasing.comp (skipIndex_strictMono p.n a d h)
  forward_half i := by
    by_cases hi : i.val = a
    · have hc : skipIndex p.n a d h i.castSucc = ⟨a, by omega⟩ := by
        ext
        simp [skipIndex, hi]
      have hs : skipIndex p.n a d h i.succ = ⟨a + d + 1, by omega⟩ := by
        ext
        simp only [skipIndex, Fin.val_succ, hi]
        split_ifs <;> omega
      rw [hc, hs]
      exact hgap
    · obtain ⟨k, hc, hs⟩ := skipIndex_consecutive p.n a d h i hi
      rw [hc, hs]
      exact p.forward_half k
  span_half := by simpa using p.span_half

@[simp] theorem deleteBetween_n
    (hgap : p.time ⟨a + d + 1, by omega⟩ - p.time ⟨a, by omega⟩ ≤ 1 / 2) :
    (p.deleteBetween a d h hgap).n = p.n - d := rfl

/-- Every retained edge is an old edge, except the specified shortcut. -/
theorem deleteBetween_maxEdge_le
    (hgap : p.time ⟨a + d + 1, by omega⟩ - p.time ⟨a, by omega⟩ ≤ 1 / 2)
    (hshort : dist (p.vertex ⟨a, by omega⟩) (p.vertex ⟨a + d + 1, by omega⟩) ≤ p.maxEdge) :
    (p.deleteBetween a d h hgap).maxEdge ≤ p.maxEdge := by
  apply Finset.sup'_le
  intro i _
  change Fin (p.n - d + 1) at i
  induction i using Fin.lastCases with
  | last =>
    simpa [edgeLength, vertex, deleteBetween] using p.edgeLength_le_maxEdge (Fin.last p.n)
  | cast i =>
    change dist (p.vertex (skipIndex p.n a d h i.castSucc))
      (p.vertex (skipIndex p.n a d h (nextIndex (p.n - d) i.castSucc))) ≤ _
    rw [nextIndex_castSucc]
    by_cases hi : i.val = a
    · have hc : skipIndex p.n a d h i.castSucc = ⟨a, by omega⟩ := by
        ext
        simp [skipIndex, hi]
      have hs : skipIndex p.n a d h i.succ = ⟨a + d + 1, by omega⟩ := by
        ext
        simp only [skipIndex, Fin.val_succ, hi]
        split_ifs <;> omega
      rw [hc, hs]
      exact hshort
    · obtain ⟨k, hc, hs⟩ := skipIndex_consecutive p.n a d h i hi
      rw [hc, hs]
      simpa only [edgeLength, nextIndex_castSucc] using p.edgeLength_le_maxEdge k.castSucc

theorem deleteBetween_count_lt
    (hgap : p.time ⟨a + d + 1, by omega⟩ - p.time ⟨a, by omega⟩ ≤ 1 / 2) (hd : 0 < d) :
    (p.deleteBetween a d h hgap).n + 1 < p.n + 1 := by
  rw [deleteBetween_n]
  omega

end InscribedPolygon
end Reeken.Geometry
