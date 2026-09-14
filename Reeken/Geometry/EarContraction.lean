import Reeken.Geometry.ParityContraction

/-! # Contraction after an actual triangular deletion

The shortened polygon is constructed from the old vertex family. Parity
cancellation identifies its closed region with the part left after deleting an
internal triangle, including when normalization later removes collinear corners.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {m : ℕ}

theorem triangle_inter_deleted_carrier (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier)
    (hdet : Plane.det (P.vertex (-1) - P.vertex (-1 - 1))
      (P.vertex 0 - P.vertex (-1 - 1)) ≠ 0) :
    (Schoenflies.triangle hdet).carrier ∩ (deleteLastAcrossDiagonal P hdiag).carrier =
      segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  rw [triangle_carrier_eq_segments, carrier_deleteLastAcrossDiagonal]
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  apply subset_antisymm
  · rintro x ⟨(hxA | hxB) | hxbase, hxQ⟩
    · rcases hxQ with hxQ | hxbase
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxQ
        have hmeet := P.edges_meet (-1 - 1) j (Ne.symm hj.2)
          ⟨by simpa only [PrePolygon.edge, e1] using hxA, hxj⟩
        rw [e1] at hmeet
        rcases hmeet with rfl | he
        · exact left_mem_segment ℝ _ _
        · exact False.elim (PrePolygon.vertex_last_notMem_edge hj.1 hj.2 (he ▸ hxj))
      · exact hxbase
    · rcases hxQ with hxQ | hxbase
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxQ
        have hmeet := P.edges_meet (-1) j (Ne.symm hj.1)
          ⟨by simpa only [PrePolygon.edge, e2] using hxB, hxj⟩
        rw [e2] at hmeet
        rcases hmeet with he | rfl
        · exact False.elim (PrePolygon.vertex_last_notMem_edge hj.1 hj.2 (he ▸ hxj))
        · exact right_mem_segment ℝ _ _
      · exact hxbase
    · rwa [segment_symm] at hxbase
  · intro x hx
    exact ⟨Or.inr (by rwa [segment_symm]), Or.inr hx⟩

theorem closed_regions_of_last_ear (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier)
    (hdet : Plane.det (P.vertex (-1) - P.vertex (-1 - 1))
      (P.vertex 0 - P.vertex (-1 - 1)) ≠ 0)
    (hTin : inside (Schoenflies.triangle hdet).carrier ⊆ inside P.carrier) :
    closure (inside (Schoenflies.triangle hdet).carrier) ∪
        closure (inside (deleteLastAcrossDiagonal P hdiag).carrier) = closure (inside P.carrier) ∧
      closure (inside (Schoenflies.triangle hdet).carrier) ∩
        closure (inside (deleteLastAcrossDiagonal P hdiag).carrier) =
          segment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  let T := (Schoenflies.triangle hdet).toPre
  let Q := deleteLastAcrossDiagonal P hdiag
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (P.pieces ++ T.pieces ++ Q.pieces) (by
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · rcases List.mem_append.mp hR with hR | hR
      · exact P.pieces_nondeg R hR
      · exact T.pieces_nondeg R hR
    · exact Q.pieces_nondeg R hR)
  have hP : ∀ R ∈ P.pieces, hgt u R.1 ≠ hgt u R.2 :=
    fun R hR ↦ hlev R (List.mem_append_left _ (List.mem_append_left _ hR))
  have hT : ∀ R ∈ T.pieces, hgt u R.1 ≠ hgt u R.2 :=
    fun R hR ↦ hlev R (List.mem_append_left _ (List.mem_append_right _ hR))
  have hQ : ∀ R ∈ Q.pieces, hgt u R.1 ≠ hgt u R.2 :=
    fun R hR ↦ hlev R (List.mem_append_right _ hR)
  have hbase : hgt u (P.vertex (-1 - 1)) ≠ hgt u (P.vertex 0) := by
    apply Ne.symm
    apply hT (P.vertex 0, P.vertex (-1 - 1))
    change (P.vertex 0, P.vertex (-1 - 1)) ∈ (Schoenflies.triangle hdet).pieces
    rw [pieces_triangle]
    simp
  have hsum : ∀ x, parity u T.pieces x + parity u Q.pieces x = parity u P.pieces x := by
    intro x
    rw [add_comm]
    exact parity_deleteLastAcrossDiagonal P hdiag hdet u x hbase
  refine ⟨closed_inside_union_of_parity_sum P T Q hu hP hT hQ hsum hTin, ?_⟩
  change closure (inside T.carrier) ∩ closure (inside Q.carrier) = _
  rw [closed_inside_inter_of_disjoint T.isSeparating_carrier Q.isSeparating_carrier
    (disjoint_inside_of_parity_sum P T Q hu hP hT hQ hsum hTin)]
  exact triangle_inter_deleted_carrier P hdiag hdet

theorem contractible_closed_inside_of_last_ear (P : PrePolygon (m + 1))
    (hdiag : Disjoint (openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) P.carrier)
    (hdet : Plane.det (P.vertex (-1) - P.vertex (-1 - 1))
      (P.vertex 0 - P.vertex (-1 - 1)) ≠ 0)
    (hTin : inside (Schoenflies.triangle hdet).carrier ⊆ inside P.carrier)
    [ContractibleSpace (closure (inside (deleteLastAcrossDiagonal P hdiag).carrier))] :
    ContractibleSpace (closure (inside P.carrier)) := by
  obtain ⟨hunion, hinter⟩ := closed_regions_of_last_ear P hdiag hdet hTin
  rw [← hunion]
  apply contractibleSpace_union_of_segment_inter isClosed_closure isClosed_closure _
    (P.vertex (-1 - 1)) (P.vertex 0) hinter
  rw [triangle_closed_inside_eq_hull]
  exact convex_convexHull ℝ _

end Reeken.Geometry
