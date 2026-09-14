import Reeken.Geometry.SimpleLoop
import Reeken.Geometry.Segments
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin

/-!
# Inscribed polygons with controlled circular order

These are exactly the finite data in conditions (†) and (‡) of Kanovei–Reeken.
Self-intersections are allowed. The number of vertices is `n + 1`.
-/

open Set
open scoped BigOperators

namespace Reeken.Geometry

/-- Cyclic successor, with the final index followed by zero. -/
def nextIndex (n : ℕ) : Fin (n + 1) → Fin (n + 1) := Fin.lastCases 0 Fin.succ

@[simp] theorem nextIndex_castSucc {n : ℕ} (i : Fin n) :
    nextIndex n i.castSucc = i.succ := by simp [nextIndex]

@[simp] theorem nextIndex_last (n : ℕ) : nextIndex n (Fin.last n) = 0 := by simp [nextIndex]

variable {E : Type*} [NormedAddCommGroup E]

structure InscribedPolygon (f : SimpleLoop E) where
  n : ℕ
  time : Fin (n + 1) → ℝ
  time_mem : ∀ i, time i ∈ Ico 0 1
  increasing : StrictMono time
  forward_half : ∀ i : Fin n, time i.succ - time i.castSucc ≤ 1 / 2
  span_half : 1 / 2 ≤ time (Fin.last n) - time 0

namespace InscribedPolygon

variable {f : SimpleLoop E} (p : InscribedPolygon f)

def vertex (i : Fin (p.n + 1)) : E := f (p.time i)

def trace [NormedSpace ℝ E] : Set E := ⋃ i, segment ℝ (p.vertex i) (p.vertex (nextIndex p.n i))

noncomputable def edgeLength (i : Fin (p.n + 1)) : ℝ :=
  dist (p.vertex i) (p.vertex (nextIndex p.n i))

noncomputable def maxEdge : ℝ := Finset.univ.sup' Finset.univ_nonempty p.edgeLength

theorem edgeLength_le_maxEdge (i : Fin (p.n + 1)) : p.edgeLength i ≤ p.maxEdge :=
  Finset.le_sup' _ (Finset.mem_univ i)

noncomputable def gap : Fin (p.n + 1) → ℝ :=
  Fin.lastCases (1 - p.time (Fin.last p.n) + p.time 0)
    (fun i ↦ p.time i.succ - p.time i.castSucc)

@[simp] theorem gap_castSucc (i : Fin p.n) :
    p.gap i.castSucc = p.time i.succ - p.time i.castSucc := by simp [gap]

@[simp] theorem gap_last : p.gap (Fin.last p.n) = 1 - p.time (Fin.last p.n) + p.time 0 := by
  simp [gap]

theorem gap_pos (i : Fin (p.n + 1)) : 0 < p.gap i := by
  induction i using Fin.lastCases with
  | last =>
    rw [gap_last]
    have hlast := (p.time_mem (Fin.last p.n)).2
    have hfirst := (p.time_mem 0).1
    linarith
  | cast i =>
    rw [gap_castSucc]
    exact sub_pos.mpr (p.increasing (by simp))

theorem gap_le_half (i : Fin (p.n + 1)) : p.gap i ≤ 1 / 2 := by
  induction i using Fin.lastCases with
  | last =>
    rw [gap_last]
    linarith [p.span_half]
  | cast i => simpa only [gap_castSucc] using p.forward_half i

noncomputable def maxGap : ℝ := Finset.univ.sup' Finset.univ_nonempty p.gap

theorem gap_le_maxGap (i : Fin (p.n + 1)) : p.gap i ≤ p.maxGap :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- Circular parameter gaps telescope to one full turn. -/
theorem sum_gap : ∑ i, p.gap i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [gap_castSucc, gap_last, Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ p.time
  have h₂ := Fin.sum_univ_castSucc p.time
  linarith

theorem one_le_count_mul_maxGap : 1 ≤ (p.n + 1 : ℝ) * p.maxGap := by
  calc
    1 = ∑ i, p.gap i := p.sum_gap.symm
    _ ≤ ∑ _i : Fin (p.n + 1), p.maxGap := Finset.sum_le_sum fun i _ ↦ p.gap_le_maxGap i
    _ = (p.n + 1 : ℝ) * p.maxGap := by simp

end InscribedPolygon
end Reeken.Geometry
