import Reeken.Geometry.InscribedPolygon
import Reeken.Geometry.UniformMesh

/-! # Explicit initial polygons satisfying both circular-order conditions -/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E]

/-- At least three equally spaced samples on a simple loop. -/
noncomputable def uniform (f : SimpleLoop E) (n : ℕ) : InscribedPolygon f := by
  have hn : 0 < ((n + 2 : ℕ) + 1 : ℝ) := by positivity
  refine {
    n := n + 2
    time := fun i ↦ meshTime (n + 2) i
    time_mem := ?_
    increasing := ?_
    forward_half := ?_
    span_half := ?_
  }
  · intro i
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hn.le
    · apply (div_lt_one hn).mpr
      exact_mod_cast i.isLt
  · intro a b hab
    apply div_lt_div_of_pos_right _ hn
    exact_mod_cast hab
  · intro i
    change meshTime (n + 2) (i + 1) - meshTime (n + 2) i ≤ 1 / 2
    rw [meshTime_step, div_le_iff₀ hn]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · change 1 / 2 ≤ meshTime (n + 2) (n + 2) - meshTime (n + 2) 0
    simp only [meshTime, Nat.cast_zero, zero_div, sub_zero]
    rw [le_div_iff₀ hn]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

@[simp] theorem uniform_n (f : SimpleLoop E) (n : ℕ) : (uniform f n).n = n + 2 := rfl

@[simp] theorem uniform_time (f : SimpleLoop E) (n : ℕ) (i : Fin (n + 2 + 1)) :
    (uniform f n).time i = meshTime (n + 2) i := rfl

theorem uniform_next_vertex (f : SimpleLoop E) (n : ℕ) (i : Fin (n + 2 + 1)) :
    (uniform f n).vertex (nextIndex (n + 2) i) = f (meshTime (n + 2) (i + 1)) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [nextIndex_last, vertex, uniform_time, Fin.val_zero, Fin.val_last]
    have h₁ : meshTime (n + 2) (n + 2 + 1) = 1 := by
      simp [meshTime, show (n + 2 : ℝ) + 1 ≠ 0 by positivity]
    rw [h₁, f.endpoint]
    simp [meshTime]
  | cast i =>
    rw [nextIndex_castSucc]
    rfl

theorem uniform_edgeLength (f : SimpleLoop E) (n : ℕ) (i : Fin (n + 2 + 1)) :
    (uniform f n).edgeLength i =
      dist (f (meshTime (n + 2) i)) (f (meshTime (n + 2) (i + 1))) := by
  change dist ((uniform f n).vertex i) ((uniform f n).vertex (nextIndex (n + 2) i)) = _
  rw [uniform_next_vertex]
  rfl

theorem uniform_trace [NormedSpace ℝ E] (f : SimpleLoop E) (n : ℕ) :
    (uniform f n).trace = meshTrace f (n + 2) := by
  change (⋃ i : Fin (n + 2 + 1), segment ℝ ((uniform f n).vertex i)
    ((uniform f n).vertex (nextIndex (n + 2) i))) = _
  apply iUnion_congr
  intro i
  rw [uniform_next_vertex]
  rfl

end Reeken.Geometry.InscribedPolygon
