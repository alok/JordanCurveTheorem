import Reeken.Geometry.EarContraction

/-! # The finite contraction induction

The induction step constructs the shorter polygon, normalizes it with a retained
vertex-count bound, and applies triangular contraction. The final theorem of this
module isolates existence of internal ears as its geometric input.
`PolygonEars.lean` establishes that input and gives unconditional contractibility.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem triangle_carrier_cyclic {a b c : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (h' : Plane.det (a - c) (b - c) ≠ 0) :
    (Schoenflies.triangle h).carrier = (Schoenflies.triangle h').carrier := by
  rw [triangle_carrier_eq_segments, triangle_carrier_eq_segments]
  ac_rfl

theorem contractible_closed_inside_of_internal_corner_diagonal {m : ℕ}
    (P : ClosedPolygon m) (hm : 0 < m) (i : ZMod (m + 3))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1))) P.carrier)
    (hTin : inside (cornerTriangle P i).carrier ⊆ inside P.carrier)
    (ih : ∀ n < m, ∀ Q : ClosedPolygon n, ContractibleSpace (closure (inside Q.carrier))) :
    ContractibleSpace (closure (inside P.carrier)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let R := P.toPre.rotate (i + 1)
  have hR : R.carrier = P.carrier := PrePolygon.carrier_rotate _ _
  have ha : R.vertex (-1 - 1) = P.vertex (i - 1) := by
    change P.vertex (i + 1 + (-1 - 1)) = P.vertex (i - 1)
    congr 1
    ring
  have hb : R.vertex (-1) = P.vertex i := by
    change P.vertex (i + 1 + (-1)) = P.vertex i
    congr 1
    ring
  have hc : R.vertex 0 = P.vertex (i + 1) := by
    change P.vertex (i + 1 + 0) = P.vertex (i + 1)
    rw [add_zero]
  have hdiagR : Disjoint (openSegment ℝ (R.vertex (-1 - 1)) (R.vertex 0)) R.carrier := by
    rw [ha, hc, hR]
    exact hdiag
  have hdet : Plane.det (R.vertex (-1) - R.vertex (-1 - 1))
      (R.vertex 0 - R.vertex (-1 - 1)) ≠ 0 := by
    rw [ha, hb, hc]
    have he : Plane.det (P.vertex i - P.vertex (i - 1)) (P.vertex (i + 1) - P.vertex (i - 1)) =
        -Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) := by
      simp [Plane.det]
      ring
    rw [he]
    exact neg_ne_zero.mpr (P.corner i)
  have hTcar : (Schoenflies.triangle hdet).carrier = (cornerTriangle P i).carrier := by
    rw [triangle_carrier_eq_segments]
    simp only [ha, hb, hc]
    unfold cornerTriangle
    rw [triangle_carrier_eq_segments]
    ac_rfl
  have hTinR : inside (Schoenflies.triangle hdet).carrier ⊆ inside R.carrier := by
    rw [hTcar, hR]
    exact hTin
  obtain ⟨n, Q, hn, hQ, -⟩ := exists_closedPolygon_le_of_prePolygon m
    (deleteLastAcrossDiagonal R hdiagR)
  have hsmall := ih n (by omega) Q
  have hcontract : ContractibleSpace (closure (inside (deleteLastAcrossDiagonal R hdiagR).carrier)) := by
    rw [← hQ]
    exact hsmall
  let := hcontract
  rw [← hR]
  exact contractible_closed_inside_of_last_ear R hdiagR hdet hTinR

/-- Conditional finite induction: the only supplied input is the geometric ear
existence statement, established for every polygon in `PolygonEars.lean`. -/
theorem contractible_closed_inside_of_internal_ears
    (hears : ∀ (m : ℕ), 0 < m → ∀ P : ClosedPolygon m, ∃ i : ZMod (m + 3),
      Disjoint (openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1))) P.carrier ∧
        inside (cornerTriangle P i).carrier ⊆ inside P.carrier) :
    ∀ (m : ℕ) (P : ClosedPolygon m), ContractibleSpace (closure (inside P.carrier)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact contractibleSpace_triangle_closed_inside P
    · obtain ⟨i, hdiag, hTin⟩ := hears m hm P
      exact contractible_closed_inside_of_internal_corner_diagonal P hm i hdiag hTin ih

end Reeken.Geometry
