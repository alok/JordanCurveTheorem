/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Square

/-! # Interior and frontier of a square

Finite coordinate excerpts from `SquareMover.lean` at the pinned upstream revision.
The point-moving construction is not included. See vendor/README.md.
-/

open Metric Set

namespace Schoenflies.Plane

/-- Each coordinate difference is bounded by the sup distance. -/
theorem abs_sub_le_supDist (z c : Plane) (l : Fin 2) : |z l - c l| ≤ supDist z c := by
  fin_cases l
  · exact abs_sub_zero_le_supDist z c
  · exact abs_sub_one_le_supDist z c

/-- Conversely, a bound on both coordinate differences bounds the sup distance. -/
theorem supDist_le_of_forall {z c : Plane} {r : ℝ} (h : ∀ l : Fin 2, |z l - c l| ≤ r) :
    supDist z c ≤ r :=
  max_le (h 0) (h 1)

/-- The sup distance is attained at one of the two coordinates. -/
theorem exists_abs_sub_eq_of_supDist_eq {z c : Plane} {r : ℝ} (h : supDist z c = r) :
    ∃ l : Fin 2, |z l - c l| = r := by
  rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
  · exact ⟨0, by rw [← h]; exact hm.symm⟩
  · exact ⟨1, by rw [← h]; exact hm.symm⟩

theorem add_smul_single_apply (z : Plane) (t : ℝ) (l : Fin 2) :
    (z + t • EuclideanSpace.single l (1 : ℝ)) l = z l + t := by
  simp [PiLp.add_apply, PiLp.smul_apply]

theorem dist_add_smul_single (z : Plane) (t : ℝ) (l : Fin 2) :
    dist (z + t • EuclideanSpace.single l (1 : ℝ)) z = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single]
  simp

/-- The interior of the closed square is the open square: a point with a coordinate at
distance exactly `r` from the centre can be pushed further out along that coordinate. -/
theorem interior_closedSquare (c : Plane) (r : ℝ) :
    interior (closedSquare c r) = openSquare c r := by
  have hsub : openSquare c r ⊆ closedSquare c r := fun z hz => show supDist z c ≤ r from hz.le
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal hsub (isOpen_openSquare c r))
  by_contra hzo
  have hzc : z ∈ closedSquare c r := interior_subset hz
  have heq : supDist z c = r := le_antisymm hzc (not_lt.1 hzo)
  obtain ⟨l, hl⟩ := exists_abs_sub_eq_of_supDist_eq heq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hr : 0 ≤ r := hl ▸ abs_nonneg _
  have key : ∀ t : ℝ, |t| < ε → |(z l - c l) + t| ≤ r := by
    intro t ht
    have hmem : z + t • EuclideanSpace.single l (1 : ℝ) ∈ closedSquare c r :=
      interior_subset (hball (by rw [Metric.mem_ball, dist_add_smul_single]; exact ht))
    have := le_trans (abs_sub_le_supDist (z + t • EuclideanSpace.single l (1 : ℝ)) c l) hmem
    rwa [add_smul_single_apply, show z l + t - c l = z l - c l + t by ring] at this
  rcases (abs_eq hr).1 hl with he | he
  · have := (abs_le.1 (key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))).2
    rw [he] at this
    linarith
  · have := (abs_le.1 (key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))).1
    rw [he] at this
    linarith

/-- The boundary of the closed square is the sup-distance sphere: the blueprint's `S`. -/
theorem frontier_closedSquare (c : Plane) (r : ℝ) :
    frontier (closedSquare c r) = {z | supDist z c = r} := by
  rw [(isClosed_closedSquare c r).frontier_eq, interior_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.1 h2)
  · intro h
    exact ⟨le_of_eq h, by rw [openSquare, mem_ofPred_eq, h]; exact lt_irrefl r⟩


end Schoenflies.Plane
