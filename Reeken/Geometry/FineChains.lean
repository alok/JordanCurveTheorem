import Reeken.Geometry.EdgeReplacementParity
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! # Arbitrarily fine subdivisions preserving the crossing count

Repeated midpoint subdivision preserves the carrier, closed-chain boundary, and
parity. It allows the inner polygon's straight edges to be subdivided even when
its normalized presentation has merged several collinear drawing edges.
-/

open Set Schoenflies

namespace Reeken.Geometry

noncomputable def bisectPiece (P : Piece) : List Piece :=
  [(P.1, midpoint ℝ P.1 P.2), (midpoint ℝ P.1 P.2, P.2)]

theorem bisectPiece_eq_splitAt (P : Piece) :
    bisectPiece P = splitAt (midpoint ℝ P.1 P.2) P := by
  rw [splitAt, Piece.interior, if_pos (midpoint_mem_openSegment (𝕜 := ℝ) P.1 P.2)]
  rfl

theorem cover_bisectPiece (P : Piece) : cover (bisectPiece P) = P.seg := by
  rw [bisectPiece_eq_splitAt, splitAt_cover]

theorem isChainFrom_bisectPiece (P : Piece) : IsChainFrom (bisectPiece P) P.1 P.2 := by
  intro f
  simp only [bisectPiece, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  linear_combination add_self_zmod_two (f (midpoint ℝ P.1 P.2))

theorem bisectPiece_nondeg {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ bisectPiece P, Q.Nondeg := by
  rw [bisectPiece_eq_splitAt]
  exact splitAt_ne _ hP

theorem dist_bisectPiece {P Q : Piece} (hQ : Q ∈ bisectPiece P) :
    dist Q.1 Q.2 = dist P.1 P.2 / 2 := by
  simp only [bisectPiece, List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl
  · simp [dist_left_midpoint, div_eq_mul_inv, mul_comm]
  · simp [dist_midpoint_right, div_eq_mul_inv, mul_comm]

noncomputable def refinePieces : ℕ → List Piece → List Piece
  | 0, L => L
  | n + 1, L => (refinePieces n L).flatMap bisectPiece

theorem cover_refinePieces (n : ℕ) (L : List Piece) : cover (refinePieces n L) = cover L := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [refinePieces, cover_flatMap]
    simp only [cover_bisectPiece]
    exact ih

theorem refinePieces_nondeg (n : ℕ) {L : List Piece} (hL : ∀ P ∈ L, P.Nondeg) :
    ∀ Q ∈ refinePieces n L, Q.Nondeg := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    intro Q hQ
    obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.mp hQ
    exact bisectPiece_nondeg (ih P hP) Q hQP

theorem isClosedChain_refinePieces (n : ℕ) {L : List Piece} (hL : IsClosedChain L) :
    IsClosedChain (refinePieces n L) := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    exact isClosedChain_replacement_arcs (foot := id) ih (fun P _ ↦ isChainFrom_bisectPiece P)

theorem refinePieces_hgt_ne (n : ℕ) {L : List Piece} {u : Plane}
    (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) :
    ∀ Q ∈ refinePieces n L, hgt u Q.1 ≠ hgt u Q.2 := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    intro Q hQ
    obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.mp hQ
    rw [bisectPiece_eq_splitAt] at hQP
    exact splitAt_hgt_ne (ih P hP) _ Q hQP

theorem parity_refinePieces (n : ℕ) {L : List Piece} {u : Plane}
    (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (x : Plane) :
    parity u (refinePieces n L) x = parity u L x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : ∀ M : List Piece, (∀ P ∈ M, hgt u P.1 ≠ hgt u P.2) →
        parity u (M.flatMap bisectPiece) x = parity u M x := by
      intro M hM
      induction M with
      | nil => rfl
      | cons P M ihM =>
        rw [List.flatMap_cons, parity_append, ihM (fun Q hQ ↦ hM Q (by simp [hQ]))]
        have hP : parity u (bisectPiece P) x = mark u P x := by
          rw [bisectPiece_eq_splitAt, parity_eq_crossings,
            crossings_splitAt (hM P (by simp)), ← parity_eq_crossings]
          simp
        rw [hP, parity_cons]
    exact (hstep _ (refinePieces_hgt_ne n hL)).trans ih

theorem dist_refinePieces_le (n : ℕ) {L : List Piece} {r : ℝ}
    (hL : ∀ P ∈ L, dist P.1 P.2 ≤ r) :
    ∀ Q ∈ refinePieces n L, dist Q.1 Q.2 ≤ r * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simpa only [refinePieces, pow_zero, mul_one] using hL
  | succ n ih =>
    intro Q hQ
    obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.mp hQ
    rw [dist_bisectPiece hQP, pow_succ]
    have h := div_le_div_of_nonneg_right (ih P hP) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

theorem exists_fine_chain (L : List Piece) (hclosed : IsClosedChain L)
    (hnd : ∀ P ∈ L, P.Nondeg) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : List Piece, cover M = cover L ∧ IsClosedChain M ∧
      (∀ Q ∈ M, Q.Nondeg) ∧ (∀ Q ∈ M, dist Q.1 Q.2 < ε) ∧
      ∀ u : Plane, (∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) → ∀ x, parity u M x = parity u L x := by
  obtain ⟨R, hRpos, hR⟩ := (isCompact_cover L).isBounded.exists_pos_norm_le
  have hbound : ∀ P ∈ L, dist P.1 P.2 ≤ 2 * R := by
    intro P hP
    have h1 := hR P.1 (mem_cover hP (left_mem_segment ℝ _ _))
    have h2 := hR P.2 (mem_cover hP (right_mem_segment ℝ _ _))
    have h := norm_sub_le P.1 P.2
    rw [dist_eq_norm]
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * R) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨refinePieces n L, cover_refinePieces n L, isClosedChain_refinePieces n hclosed,
    refinePieces_nondeg n hnd, ?_, fun u hu x ↦ parity_refinePieces n hu x⟩
  intro Q hQ
  have hsmall : (2 * R) * (1 / 2 : ℝ) ^ n < ε := by
    have h := (lt_div_iff₀ (show 0 < 2 * R by positivity)).mp hn
    simpa only [mul_comm] using h
  exact (dist_refinePieces_le n hbound Q hQ).trans_lt hsmall

end Reeken.Geometry
