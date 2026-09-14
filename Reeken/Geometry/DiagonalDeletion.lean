import Reeken.Geometry.PolygonNormalization
import Reeken.Geometry.EmptyEarDiagonal

/-! # Deleting a polygon corner across a diagonal

An open diagonal disjoint from the old carrier permits deletion of the intervening
corner. The intermediate polygon may have redundant vertices; normalization then
produces a closed polygon with strictly fewer vertices.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem prePolygon_vertex_mem_edge_ends {m : ℕ} (P : PrePolygon m)
    {i j : ZMod (m + 3)} (hx : P.vertex i ∈ P.edge j) :
    P.vertex i ∈ ({P.vertex j, P.vertex (j + 1)} : Set Plane) := by
  by_cases hij : i = j
  · exact Or.inl (congrArg P.vertex hij)
  · exact P.edges_meet j i (Ne.symm hij) ⟨hx, left_mem_segment ℝ _ _⟩

theorem segment_meets_only_ends_of_open_disjoint {a b : Plane} {S : Set Plane}
    (h : Disjoint (openSegment ℝ a b) S) :
    segment ℝ a b ∩ S ⊆ ({a, b} : Set Plane) := by
  rintro x ⟨hx, hxS⟩
  by_cases ha : x = a
  · exact Or.inl ha
  by_cases hb : x = b
  · exact Or.inr hb
  exact False.elim (disjoint_left.mp h (mem_openSegment_of_ne_left_right (Ne.symm ha) (Ne.symm hb) hx) hxS)

variable {m : ℕ}

def deleteLastAcrossDiagonal (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier) :
    PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := PrePolygon.dropVertex_injective
  edges_meet := by
    intro j k hjk
    have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
    have hlast : ∀ t : ZMod (m + 3), t.val + 1 = m + 3 →
        segment ℝ (P.dropVertex t) (P.dropVertex (t + 1)) =
          segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
      intro t ht
      rw [PrePolygon.dropVertex, PrePolygon.dropVertex, PrePolygon.emb_eq_last ht,
        PrePolygon.emb_succ_last ht]
    have hmeet := segment_meets_only_ends_of_open_disjoint hdiag
    rcases eq_or_lt_of_le hjv with hj | hj
    · rcases eq_or_lt_of_le hkv with hk | hk
      · exact False.elim (hjk (ZMod.val_injective _ (by omega)))
      rw [hlast j hj, PrePolygon.dropVertex_edge_of_lt hk]
      have he : ({P.dropVertex j, P.dropVertex (j + 1)} : Set Plane) =
          {P.vertex (-1 - 1), P.vertex 0} := by
        rw [PrePolygon.dropVertex, PrePolygon.dropVertex, PrePolygon.emb_eq_last hj,
          PrePolygon.emb_succ_last hj]
      rw [he]
      exact fun _ hx ↦ hmeet ⟨hx.1, PrePolygon.edge_subset_carrier _ hx.2⟩
    · rw [PrePolygon.dropVertex_edge_of_lt hj]
      rcases eq_or_lt_of_le hkv with hk | hk
      · rw [hlast k hk]
        intro x hx
        have hxends := hmeet ⟨hx.2, PrePolygon.edge_subset_carrier _ hx.1⟩
        have he : ({P.dropVertex j, P.dropVertex (j + 1)} : Set Plane) =
            {P.vertex (PrePolygon.emb j), P.vertex (PrePolygon.emb j + 1)} := by
          rw [PrePolygon.dropVertex, PrePolygon.dropVertex, PrePolygon.emb_succ_of_lt hj]
        rw [he]
        rcases hxends with rfl | rfl
        · exact prePolygon_vertex_mem_edge_ends P hx.1
        · exact prePolygon_vertex_mem_edge_ends P hx.1
      · rw [PrePolygon.dropVertex_edge_of_lt hk]
        have he : ({P.dropVertex j, P.dropVertex (j + 1)} : Set Plane) =
            {P.vertex (PrePolygon.emb j), P.vertex (PrePolygon.emb j + 1)} := by
          rw [PrePolygon.dropVertex, PrePolygon.dropVertex, PrePolygon.emb_succ_of_lt hj]
        rw [he]
        exact P.edges_meet _ _ (fun he ↦ hjk (PrePolygon.emb_injective he))

theorem carrier_deleteLastAcrossDiagonal (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier) :
    (deleteLastAcrossDiagonal P hdiag).carrier =
      (⋃ (j : ZMod (m + 1 + 3)) (_ : j ≠ -1 ∧ j ≠ -1 - 1), P.edge j) ∪
        segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  have hlast : ∀ t : ZMod (m + 3), t.val + 1 = m + 3 →
      (deleteLastAcrossDiagonal P hdiag).edge t =
        segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
    intro t ht
    change segment ℝ (P.dropVertex t) (P.dropVertex (t + 1)) = _
    rw [PrePolygon.dropVertex, PrePolygon.dropVertex, PrePolygon.emb_eq_last ht,
      PrePolygon.emb_succ_last ht]
  have hord : ∀ t : ZMod (m + 3), t.val + 1 < m + 3 →
      (deleteLastAcrossDiagonal P hdiag).edge t = P.edge (PrePolygon.emb t) :=
    fun _ ht ↦ PrePolygon.dropVertex_edge_of_lt ht
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with he | he
    · exact Or.inr (hlast j he ▸ hj)
    · left
      exact mem_iUnion.mpr ⟨PrePolygon.emb j,
        mem_iUnion.mpr ⟨PrePolygon.emb_ne_of_lt he, hord j he ▸ hj⟩⟩
  · rintro (hx | hx)
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, ht, he⟩ := PrePolygon.exists_emb_eq hj.1 hj.2
      apply mem_iUnion.mpr
      exact ⟨t, by rw [hord t ht, he]; exact hxj⟩
    · let t : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3))
      have ht : t.val + 1 = m + 3 := by
        dsimp [t]
        rw [ZMod.val_cast_of_lt (by omega)]
      exact mem_iUnion.mpr ⟨t, (hlast t ht).symm ▸ hx⟩

theorem exists_smaller_polygon_of_last_diagonal (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier) :
    ∃ (n : ℕ) (Q : ClosedPolygon n), n < m + 1 ∧
      Q.carrier = (⋃ (j : ZMod (m + 1 + 3)) (_ : j ≠ -1 ∧ j ≠ -1 - 1), P.edge j) ∪
        segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) ∧ range Q.vertex ⊆ range P.vertex := by
  obtain ⟨n, Q, hn, hQ, hv⟩ :=
    exists_closedPolygon_le_of_prePolygon m (deleteLastAcrossDiagonal P hdiag)
  refine ⟨n, Q, by omega, hQ.trans (carrier_deleteLastAcrossDiagonal P hdiag), ?_⟩
  intro x hx
  obtain ⟨j, rfl⟩ := hv hx
  exact ⟨PrePolygon.emb j, rfl⟩

theorem exists_smaller_polygon_of_corner_diagonal {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m)
    (i : ZMod (m + 3))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1))) P.carrier) :
    ∃ (n : ℕ) (Q : ClosedPolygon n), n < m ∧
      Q.carrier = (⋃ (j : ZMod (m + 3)) (_ : j ≠ i ∧ j ≠ i - 1), P.edge j) ∪
        segment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) ∧
      range Q.vertex ⊆ range P.vertex := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let R := P.toPre.rotate (i + 1)
  have hR : R.carrier = P.carrier := PrePolygon.carrier_rotate _ _
  have hdiagR : Disjoint (openSegment ℝ (R.vertex (-1 - 1)) (R.vertex 0)) R.carrier := by
    change Disjoint (openSegment ℝ (P.vertex (i + 1 + (-1 - 1))) (P.vertex (i + 1 + 0))) R.carrier
    rw [show i + 1 + (-1 - 1) = i - 1 by ring, add_zero, hR]
    exact hdiag
  obtain ⟨n, Q, hn, hQ, hv⟩ := exists_smaller_polygon_of_last_diagonal R hdiagR
  refine ⟨n, Q, hn, ?_, ?_⟩
  · rw [hQ]
    have he : (⋃ (j : ZMod (m + 1 + 3)) (_ : j ≠ -1 ∧ j ≠ -1 - 1), R.edge j) =
        ⋃ (j : ZMod (m + 1 + 3)) (_ : j ≠ i ∧ j ≠ i - 1), P.edge j := by
      have hedge : ∀ j, R.edge j = P.edge (i + 1 + j) := by
        intro j
        change segment ℝ (P.vertex (i + 1 + j)) (P.vertex (i + 1 + (j + 1))) = _
        rw [← add_assoc]
        rfl
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨i + 1 + j,
          ⟨fun he ↦ hj.1 (by linear_combination he),
           fun he ↦ hj.2 (by linear_combination he)⟩, hedge j ▸ hxj⟩
      · intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        refine mem_iUnion₂.mpr ⟨j - (i + 1),
          ⟨fun he ↦ hj.1 (by linear_combination he),
           fun he ↦ hj.2 (by linear_combination he)⟩, ?_⟩
        rw [hedge, add_sub_cancel]
        exact hxj
    rw [he]
    congr 2
    · change P.vertex (i + 1 + (-1 - 1)) = P.vertex (i - 1)
      congr 1
      ring
    · change P.vertex (i + 1 + 0) = P.vertex (i + 1)
      rw [add_zero]
  · intro x hx
    obtain ⟨j, rfl⟩ := hv hx
    exact ⟨i + 1 + j, rfl⟩

theorem exists_smaller_polygon_of_empty_corner {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m)
    (i : ZMod (m + 3))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) :
    ∃ (n : ℕ) (Q : ClosedPolygon n), n < m ∧
      Q.carrier = (⋃ (j : ZMod (m + 3)) (_ : j ≠ i ∧ j ≠ i - 1), P.edge j) ∪
        segment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) ∧
      range Q.vertex ⊆ range P.vertex := by
  apply exists_smaller_polygon_of_corner_diagonal P hm i
  rw [openSegment_symm ℝ (P.vertex (i - 1)) (P.vertex (i + 1))]
  exact empty_corner_base_disjoint_carrier P hm i hempty

end Reeken.Geometry
