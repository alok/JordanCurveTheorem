/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SquareFrontier
import Schoenflies.Subdivide

/-! # The four sides of a square

Finite geometric excerpts from `ModelCurve.lean` and `ArcComplementPrep.lean`
at the pinned upstream revision. See vendor/README.md for the extraction ledger.
-/

open Metric Set

namespace Schoenflies

/-- A horizontal segment: constant second coordinate, first coordinate sweeping a real
segment. -/
theorem mem_segment_horiz {u v c : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk u c) (Plane.mk v c) ↔ x 1 = c ∧ x 0 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      simp [smul_eq_mul]
  · rintro ⟨hx1, p, q, hp, hq, hpq, hx0⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk u c + q • Plane.mk v c) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, ← hx0]
      simp [smul_eq_mul]
    · change (p • Plane.mk u c + q • Plane.mk v c) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, hx1]
      linear_combination c * hpq

/-- A vertical segment: constant first coordinate, second coordinate sweeping a real
segment. -/
theorem mem_segment_vert {c u v : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk c u) (Plane.mk c v) ↔ x 0 = c ∧ x 1 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      simp [smul_eq_mul]
  · rintro ⟨hx0, p, q, hp, hq, hpq, hx1⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk c u + q • Plane.mk c v) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, hx0]
      linear_combination c * hpq
    · change (p • Plane.mk c u + q • Plane.mk c v) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, ← hx1]
      simp [smul_eq_mul]

namespace Plane

variable {c z : Plane} {r : ℝ}

/-- The sup distance in coordinates. -/
theorem supDist_eq_max (z c : Plane) : supDist z c = max |z 0 - c 0| |z 1 - c 1| := rfl

theorem mem_frontier_closedSquare :
    z ∈ frontier (closedSquare c r) ↔ max |z 0 - c 0| |z 1 - c 1| = r := by
  rw [frontier_closedSquare]
  exact Iff.rfl

/-- A point whose first coordinate is extreme and whose second is dominated is on the
boundary. -/
theorem mem_frontier_closedSquare_of_fst (h0 : |z 0 - c 0| = r) (h1 : |z 1 - c 1| ≤ r) :
    z ∈ frontier (closedSquare c r) :=
  mem_frontier_closedSquare.2 (by rw [max_eq_left (h0 ▸ h1), h0])

/-- The same with the roles of the two coordinates exchanged. -/
theorem mem_frontier_closedSquare_of_snd (h1 : |z 1 - c 1| = r) (h0 : |z 0 - c 0| ≤ r) :
    z ∈ frontier (closedSquare c r) :=
  mem_frontier_closedSquare.2 (by rw [max_eq_right (h1 ▸ h0), h1])

/-- The north-east corner of the square of radius `r` about `c`. -/
def sqNE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 + r)

/-- The north-west corner. -/
def sqNW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 + r)

/-- The south-west corner. -/
def sqSW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 - r)

/-- The south-east corner. -/
def sqSE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 - r)

@[simp] theorem sqNE_zero : sqNE c r 0 = c 0 + r := rfl
@[simp] theorem sqNE_one : sqNE c r 1 = c 1 + r := rfl
@[simp] theorem sqNW_zero : sqNW c r 0 = c 0 - r := rfl
@[simp] theorem sqNW_one : sqNW c r 1 = c 1 + r := rfl
@[simp] theorem sqSW_zero : sqSW c r 0 = c 0 - r := rfl
@[simp] theorem sqSW_one : sqSW c r 1 = c 1 - r := rfl
@[simp] theorem sqSE_zero : sqSE c r 0 = c 0 + r := rfl
@[simp] theorem sqSE_one : sqSE c r 1 = c 1 - r := rfl

/-- A real number is within `r` of `a` exactly when it lies on the segment from `a - r` to
`a + r`, in either order. Stated through `uIcc` so that the two orders are one lemma. -/
theorem mem_segment_abs {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a - r) (a + r) ↔ |x - a| ≤ r := by
  rw [segment_eq_Icc (by linarith), mem_Icc, abs_le]
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem mem_segment_abs' {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a + r) (a - r) ↔ |x - a| ≤ r := by
  rw [segment_symm]; exact mem_segment_abs hr

/-- The top side. -/
theorem mem_seg_top (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNE c r) (sqNW c r) ↔ z 1 = c 1 + r ∧ |z 0 - c 0| ≤ r := by
  rw [sqNE, sqNW, mem_segment_horiz, mem_segment_abs' hr]

/-- The left side. -/
theorem mem_seg_left (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNW c r) (sqSW c r) ↔ z 0 = c 0 - r ∧ |z 1 - c 1| ≤ r := by
  rw [sqNW, sqSW, mem_segment_vert, mem_segment_abs' hr]

/-- The bottom side. -/
theorem mem_seg_bottom (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSW c r) (sqSE c r) ↔ z 1 = c 1 - r ∧ |z 0 - c 0| ≤ r := by
  rw [sqSW, sqSE, mem_segment_horiz, mem_segment_abs hr]

/-- The right side. -/
theorem mem_seg_right (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSE c r) (sqNE c r) ↔ z 0 = c 0 + r ∧ |z 1 - c 1| ≤ r := by
  rw [sqSE, sqNE, mem_segment_vert, mem_segment_abs hr]

/-- **The boundary of a square is the union of its four sides.** -/
theorem mem_frontier_closedSquare_iff_sides (hr : 0 ≤ r) :
    z ∈ frontier (closedSquare c r) ↔
      z ∈ segment ℝ (sqNE c r) (sqNW c r) ∨ z ∈ segment ℝ (sqNW c r) (sqSW c r) ∨
      z ∈ segment ℝ (sqSW c r) (sqSE c r) ∨ z ∈ segment ℝ (sqSE c r) (sqNE c r) := by
  rw [mem_seg_top hr, mem_seg_left hr, mem_seg_bottom hr, mem_seg_right hr,
    mem_frontier_closedSquare]
  constructor
  · intro h
    have h0 : |z 0 - c 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |z 1 - c 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, h1⟩))
      · exact Or.inr (Or.inl ⟨by linarith, h1⟩)
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inl ⟨by linarith, h0⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h0⟩))
  · rintro (⟨h1, h0⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h0, h1⟩)
    · have hz : |z 1 - c 1| = r := by rw [h1, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by
        rw [h0, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]
    · have hz : |z 1 - c 1| = r := by
        rw [h1, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by rw [h0, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]

end Plane

open Plane

/-- The four sides of the square of `ℓ^∞`-radius `r` about `c`, as `Piece`s, in the same cyclic
order as `squarePolygon`. -/
def squarePieces (c : Plane) (r : ℝ) : List Piece :=
  [(sqNE c r, sqNW c r), (sqNW c r, sqSW c r), (sqSW c r, sqSE c r), (sqSE c r, sqNE c r)]

theorem cover_squarePieces (c : Plane) (hr : 0 ≤ r) :
    cover (squarePieces c r) = frontier (closedSquare c r) := by
  ext z
  rw [Plane.mem_frontier_closedSquare_iff_sides hr]
  simp only [squarePieces, cover_cons, cover_nil, Piece.seg, mem_union, mem_empty_iff_false,
    or_false]

theorem squarePieces_nondeg (c : Plane) (hr : 0 < r) :
    ∀ P ∈ squarePieces c r, P.Nondeg := by
  have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
  have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
  intro P hP
  simp only [squarePieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact hfst _ _ (by simp; linarith)
  · exact hsnd _ _ (by simp; linarith)
  · exact hfst _ _ (by simp; linarith)
  · exact hsnd _ _ (by simp; linarith)


end Schoenflies
