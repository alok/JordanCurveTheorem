import Reeken.Geometry.InscribedPolygon

/-! # Retaining a contiguous interval of vertices in loop cutting -/

namespace Reeken.Geometry

def sliceIndex {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (i : Fin (b.val - a.val + 1)) : Fin (n + 1) :=
  ⟨a.val + i.val, by have := i.isLt; have := b.isLt; omega⟩

@[simp] theorem sliceIndex_zero {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    sliceIndex a b hab 0 = a := by ext; simp [sliceIndex]

@[simp] theorem sliceIndex_last {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    sliceIndex a b hab (Fin.last (b.val - a.val)) = b := by
  ext
  simp only [sliceIndex, Fin.val_last]
  exact Nat.add_sub_of_le hab

theorem sliceIndex_strictMono {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    StrictMono (sliceIndex a b hab) := by
  intro i j hij
  change a.val + i.val < a.val + j.val
  exact Nat.add_lt_add_left hij _

namespace InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E}
variable (p : InscribedPolygon f) (a b : Fin (p.n + 1)) (hab : a ≤ b)

/-- Keep the interval from `a` to `b`, and close it with the shortcut `b` to `a`.
The retained interval must span at least half the parameter circle. -/
def slice (hspan : 1 / 2 ≤ p.time b - p.time a) : InscribedPolygon f where
  n := b.val - a.val
  time i := p.time (sliceIndex a b hab i)
  time_mem i := p.time_mem _
  increasing := p.increasing.comp (sliceIndex_strictMono a b hab)
  forward_half i := by
    let k : Fin p.n := ⟨a.val + i.val, by
      have := i.isLt
      have := b.isLt
      omega⟩
    have hs : sliceIndex a b hab i.succ = k.succ := by
      ext
      simp [sliceIndex, k, Nat.add_assoc]
    have hc : sliceIndex a b hab i.castSucc = k.castSucc := rfl
    rw [hs, hc]
    exact p.forward_half k
  span_half := by simpa using hspan

@[simp] theorem slice_n (hspan : 1 / 2 ≤ p.time b - p.time a) :
    (p.slice a b hab hspan).n = b.val - a.val := rfl

@[simp] theorem slice_time (hspan : 1 / 2 ≤ p.time b - p.time a)
    (i : Fin (b.val - a.val + 1)) :
    (p.slice a b hab hspan).time i = p.time (sliceIndex a b hab i) := rfl

/-- The only new edge is the closing shortcut. -/
theorem slice_maxEdge_le (hspan : 1 / 2 ≤ p.time b - p.time a)
    (hshort : dist (p.vertex a) (p.vertex b) ≤ p.maxEdge) :
    (p.slice a b hab hspan).maxEdge ≤ p.maxEdge := by
  apply Finset.sup'_le
  intro i _
  change Fin (b.val - a.val + 1) at i
  induction i using Fin.lastCases with
  | last =>
    simpa [edgeLength, vertex, slice, dist_comm] using hshort
  | cast i =>
    let k : Fin p.n := ⟨a.val + i.val, by
      have := i.isLt
      have := b.isLt
      omega⟩
    have hs : sliceIndex a b hab i.succ = k.succ := by
      ext
      simp [sliceIndex, k, Nat.add_assoc]
    have hc : sliceIndex a b hab i.castSucc = k.castSucc := rfl
    change dist (p.vertex (sliceIndex a b hab i.castSucc))
      (p.vertex (sliceIndex a b hab (nextIndex (b.val - a.val) i.castSucc))) ≤ _
    rw [nextIndex_castSucc, hs, hc]
    simpa only [edgeLength, nextIndex_castSucc] using p.edgeLength_le_maxEdge k.castSucc

theorem slice_count_lt (hspan : 1 / 2 ≤ p.time b - p.time a)
    (hproper : 0 < a.val ∨ b.val < p.n) :
    (p.slice a b hab hspan).n + 1 < p.n + 1 := by
  rw [slice_n]
  have := b.isLt
  omega

end InscribedPolygon
end Reeken.Geometry
