import Reeken.Geometry.DiagonalDeletion
import Schoenflies.PrePolygonSep

/-! # Parity under deletion across a diagonal

Deleting a corner replaces its two incident edges by one diagonal. The old
polygon's parity is the sum of the shortened polygon's parity and the corner
triangle's parity; the diagonal is counted twice and cancels.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {m : ℕ}

def retainedPieces (P : PrePolygon (m + 1)) : List Piece :=
  (List.range (m + 2)).map fun j : ℕ ↦
    (P.vertex (j : ZMod (m + 1 + 3)), P.vertex ((j : ZMod (m + 1 + 3)) + 1))

theorem pieces_eq_retained_append (P : PrePolygon (m + 1)) :
    P.pieces = retainedPieces P ++
      [(P.vertex (-1 - 1), P.vertex (-1)), (P.vertex (-1), P.vertex 0)] := by
  rw [PrePolygon.pieces, List.range_succ, List.range_succ, List.map_append, List.map_append]
  simp only [List.map_singleton, List.append_assoc]
  rw [← PrePolygon.neg_two_eq_cast, ← PrePolygon.neg_one_eq_cast]
  simp only [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring,
    neg_add_cancel, List.singleton_append]
  rfl

theorem pieces_deleteLastAcrossDiagonal (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier) :
    (deleteLastAcrossDiagonal P hdiag).pieces = retainedPieces P ++
      [(P.vertex (-1 - 1), P.vertex 0)] := by
  rw [PrePolygon.pieces, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hjlt : j < m + 2 := List.mem_range.mp hj
    have hjv : ((j : ℕ) : ZMod (m + 3)).val + 1 < m + 3 := by
      rw [ZMod.val_cast_of_lt (by omega)]
      omega
    change (P.vertex (PrePolygon.emb (j : ZMod (m + 3))),
      P.vertex (PrePolygon.emb ((j : ZMod (m + 3)) + 1))) = _
    rw [PrePolygon.emb_succ_of_lt hjv]
    have he : PrePolygon.emb (j : ZMod (m + 3)) = (j : ZMod (m + 1 + 3)) := by
      rw [PrePolygon.emb, ZMod.val_cast_of_lt (by omega)]
    rw [he]
  · have hjv : (((m + 2 : ℕ) : ZMod (m + 3))).val + 1 = m + 3 := by
      rw [ZMod.val_cast_of_lt (by omega)]
    change [(P.vertex (PrePolygon.emb ((m + 2 : ℕ) : ZMod (m + 3))),
      P.vertex (PrePolygon.emb (((m + 2 : ℕ) : ZMod (m + 3)) + 1)))] = _
    rw [PrePolygon.emb_eq_last hjv, PrePolygon.emb_succ_last hjv]

theorem pieces_triangle {a b c : Plane} (h : Plane.det (b - a) (c - a) ≠ 0) :
    (Schoenflies.triangle h).pieces = [(a, b), (b, c), (c, a)] := rfl

theorem parity_deleteLastAcrossDiagonal (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier)
    (hdet : Plane.det (P.vertex (-1) - P.vertex (-1 - 1))
      (P.vertex 0 - P.vertex (-1 - 1)) ≠ 0)
    (u x : Plane) (hbase : hgt u (P.vertex (-1 - 1)) ≠ hgt u (P.vertex 0)) :
    parity u (deleteLastAcrossDiagonal P hdiag).pieces x +
      parity u (Schoenflies.triangle hdet).pieces x = parity u P.pieces x := by
  rw [pieces_deleteLastAcrossDiagonal, pieces_triangle, pieces_eq_retained_append]
  simp only [parity_append, parity_cons, parity_nil, add_zero, mark_swap hbase]
  have hcancel : ∀ z : ZMod 2, z + z = 0 := by decide
  linear_combination hcancel (mark u (P.vertex (-1 - 1), P.vertex 0) x)

end Reeken.Geometry
