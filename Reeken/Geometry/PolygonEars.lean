import Reeken.Geometry.MinimalDiagonal
import Reeken.Geometry.PolygonContractionInduction

/-! # Internal ears and finite polygon contraction

A minimal-span diagonal closes an arc of two edges, producing an internal
triangle. This supplies the geometric ear hypothesis to the contraction induction.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem preTriangle_carrier_eq_segments (T : PrePolygon 0) :
    T.carrier = segment ℝ (T.vertex 0) (T.vertex 1) ∪
      segment ℝ (T.vertex 1) (T.vertex 2) ∪ segment ℝ (T.vertex 2) (T.vertex 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hc : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hc j with rfl | rfl | rfl
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hj)
    · exact Or.inr hj
  · rintro ((hx | hx) | hx)
    · exact PrePolygon.edge_subset_carrier (P := T) 0 hx
    · exact PrePolygon.edge_subset_carrier (P := T) 1 hx
    · exact PrePolygon.edge_subset_carrier (P := T) 2 hx

theorem closeArc_zero_carrier {m : ℕ} (P : ClosedPolygon m) (a : ZMod (m + 3))
    (hlen : 0 + 2 ≤ m + 1)
    (hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (0 + 2 : ℕ)))) P.carrier) :
    (closeArc P.toPre a 0 hlen hdiag).carrier = (cornerTriangle P (a + 1)).carrier := by
  rw [preTriangle_carrier_eq_segments]
  change segment ℝ (P.vertex (a + ((0 : ZMod 3).val : ZMod (m + 3))))
      (P.vertex (a + ((1 : ZMod 3).val : ZMod (m + 3)))) ∪
    segment ℝ (P.vertex (a + ((1 : ZMod 3).val : ZMod (m + 3))))
      (P.vertex (a + ((2 : ZMod 3).val : ZMod (m + 3)))) ∪
    segment ℝ (P.vertex (a + ((2 : ZMod 3).val : ZMod (m + 3))))
      (P.vertex (a + ((0 : ZMod 3).val : ZMod (m + 3)))) = _
  norm_num only [ZMod.val_zero, ZMod.val_one, ZMod.val_natCast, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero]
  rw [show (2 : ZMod 3).val = 2 by decide]
  unfold cornerTriangle
  rw [triangle_carrier_eq_segments, show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by ring]
  norm_num only [Nat.cast_ofNat]
  ac_rfl

theorem exists_internal_ear {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m) :
    ∃ i : ZMod (m + 3),
      Disjoint (openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1))) P.carrier ∧
      inside (cornerTriangle P i).carrier ⊆ inside P.carrier := by
  obtain ⟨a, hin⟩ := exists_two_edge_internal_diagonal P.toPre hm
  have hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + 2))) P.carrier :=
    disjoint_left.mpr fun _ hx hxP ↦ (hin hx).1 hxP
  have hlen : 0 + 2 ≤ m + 1 := by omega
  have hsub := closeArc_inside_subset P.toPre a 0 hlen hdiag hin
  have hcar := closeArc_zero_carrier P a hlen hdiag
  rw [hcar] at hsub
  refine ⟨a + 1, ?_, hsub⟩
  rw [show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by ring]
  exact hdiag

/-- The closed inside of every finite simple polygon is contractible. -/
theorem contractibleSpace_closed_inside (m : ℕ) (P : ClosedPolygon m) :
    ContractibleSpace (closure (inside P.carrier)) :=
  contractible_closed_inside_of_internal_ears (fun _ hm P ↦ exists_internal_ear P hm) m P

end Reeken.Geometry
