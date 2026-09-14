import Reeken.Geometry.DiagonalSpan
import Reeken.Geometry.EnclosedPolygon

/-! # Closing one boundary arc with an internal diagonal

The vertex family uses exactly the consecutive old vertices of the chosen arc.
Only its final edge is new. Thus the result is a simple polygon with a controlled
number of vertices, without requiring removal of collinear corners.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {m l : ℕ}

def arcIndex (a : ZMod (m + 3)) (j : ZMod (l + 3)) : ZMod (m + 3) := a + (j.val : ZMod (m + 3))

theorem arcIndex_injective (a : ZMod (m + 3)) (hlen : l + 2 ≤ m + 1) :
    Function.Injective (arcIndex (l := l) a) := by
  intro i j he
  apply ZMod.val_injective
  apply ClosedPolygon.natCast_inj (m := m) (by have := ZMod.val_lt i; omega)
    (by have := ZMod.val_lt j; omega)
  exact add_left_cancel he

theorem arcIndex_succ (a : ZMod (m + 3)) {j : ZMod (l + 3)} (hj : j.val + 1 < l + 3) :
    arcIndex a (j + 1) = arcIndex a j + 1 := by
  rw [arcIndex, arcIndex, PrePolygon.val_succ_of_lt hj, Nat.cast_add, Nat.cast_one, add_assoc]

theorem arcIndex_last (a : ZMod (m + 3)) {j : ZMod (l + 3)} (hj : j.val + 1 = l + 3) :
    arcIndex a j = a + ((l + 2 : ℕ) : ZMod (m + 3)) ∧ arcIndex a (j + 1) = a := by
  constructor
  · rw [arcIndex, show j.val = l + 2 by omega]
  · rw [arcIndex, PrePolygon.val_succ_last hj, Nat.cast_zero, add_zero]

def closeArc (P : PrePolygon m) (a : ZMod (m + 3)) (l : ℕ) (hlen : l + 2 ≤ m + 1)
    (hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ)))) P.carrier) :
    PrePolygon l where
  vertex j := P.vertex (arcIndex a j)
  vertex_inj := P.vertex_inj.comp (arcIndex_injective a hlen)
  edges_meet := by
    intro j k hjk
    have hjv : j.val + 1 ≤ l + 3 := ZMod.val_lt j
    have hkv : k.val + 1 ≤ l + 3 := ZMod.val_lt k
    have hmeet : segment ℝ (P.vertex (a + (l + 2 : ℕ))) (P.vertex a) ∩ P.carrier ⊆
        ({P.vertex (a + (l + 2 : ℕ)), P.vertex a} : Set Plane) := by
      apply segment_meets_only_ends_of_open_disjoint
      rwa [openSegment_symm]
    rcases eq_or_lt_of_le hjv with hj | hj
    · obtain ⟨hej, hej1⟩ := arcIndex_last a hj
      rw [hej, hej1]
      rcases eq_or_lt_of_le hkv with hk | hk
      · exact False.elim (hjk (ZMod.val_injective _ (by omega)))
      rw [arcIndex_succ a hk]
      exact fun x hx ↦ hmeet ⟨hx.1, PrePolygon.edge_subset_carrier _ hx.2⟩
    · rw [arcIndex_succ a hj]
      rcases eq_or_lt_of_le hkv with hk | hk
      · obtain ⟨hek, hek1⟩ := arcIndex_last a hk
        rw [hek, hek1]
        intro x hx
        have hxends := hmeet ⟨hx.2, PrePolygon.edge_subset_carrier _ hx.1⟩
        rcases hxends with rfl | rfl
        · exact prePolygon_vertex_mem_edge_ends P hx.1
        · exact prePolygon_vertex_mem_edge_ends P hx.1
      · rw [arcIndex_succ a hk]
        exact P.edges_meet _ _ (fun he ↦ hjk (arcIndex_injective a hlen he))

theorem closeArc_edge_of_lt (P : PrePolygon m) (a : ZMod (m + 3)) (l : ℕ)
    (hlen : l + 2 ≤ m + 1)
    (hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ)))) P.carrier)
    {j : ZMod (l + 3)} (hj : j.val + 1 < l + 3) :
    (closeArc P a l hlen hdiag).edge j = P.edge (arcIndex a j) := by
  change segment ℝ (P.vertex (arcIndex a j)) (P.vertex (arcIndex a (j + 1))) = _
  rw [arcIndex_succ a hj]
  rfl

theorem closeArc_edge_last (P : PrePolygon m) (a : ZMod (m + 3)) (l : ℕ)
    (hlen : l + 2 ≤ m + 1)
    (hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ)))) P.carrier)
    {j : ZMod (l + 3)} (hj : j.val + 1 = l + 3) :
    (closeArc P a l hlen hdiag).edge j =
      segment ℝ (P.vertex (a + (l + 2 : ℕ))) (P.vertex a) := by
  obtain ⟨hej, hej1⟩ := arcIndex_last a hj
  change segment ℝ (P.vertex (arcIndex a j)) (P.vertex (arcIndex a (j + 1))) = _
  rw [hej, hej1]

theorem closeArc_inside_subset (P : PrePolygon m) (a : ZMod (m + 3)) (l : ℕ)
    (hlen : l + 2 ≤ m + 1)
    (hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ)))) P.carrier)
    (hin : openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ))) ⊆ inside P.carrier) :
    inside (closeArc P a l hlen hdiag).carrier ⊆ inside P.carrier := by
  apply inside_subset_inside_of_carrier_subset_closed_inside P.isSeparating_carrier
    (closeArc P a l hlen hdiag).isClosed_carrier
  have hP : P.carrier ⊆ closure (inside P.carrier) :=
    fun _ hx ↦ frontier_subset_closure (P.isSeparating_carrier.frontier_inside.symm ▸ hx)
  have hbase : segment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ))) ⊆ closure (inside P.carrier) :=
    (openSegment_subset_iff_segment_subset (hP (P.vertex_mem_carrier a))
      (hP (P.vertex_mem_carrier _))).mp (hin.trans subset_closure)
  intro x hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  have hjv : j.val + 1 ≤ l + 3 := ZMod.val_lt j
  rcases eq_or_lt_of_le hjv with hj | hj
  · rw [closeArc_edge_last P a l hlen hdiag hj, segment_symm] at hxj
    exact hbase hxj
  · rw [closeArc_edge_of_lt P a l hlen hdiag hj] at hxj
    exact hP (PrePolygon.edge_subset_carrier _ hxj)

end Reeken.Geometry
