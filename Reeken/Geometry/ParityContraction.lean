import Reeken.Geometry.DiagonalParity
import Reeken.Geometry.ConvexAttachment

/-! # Closed regions from a parity cancellation

If a smaller polygon and an internal triangle have parities adding to the original
polygon's parity, their closed insides cover the original closed inside. Their
open insides are disjoint, so the closed intersection is their common boundary.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem dense_compl_of_isSeparating {C : Set Plane} (hC : IsSeparating C) : Dense Cᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, ← hC.frontier_inside, ← frontier_compl]
  exact interior_frontier hC.isOpen_inside.isClosed_compl

theorem closure_inter_dense_of_isOpen {X : Type*} [TopologicalSpace X] {U D : Set X}
    (hU : IsOpen U) (hD : Dense D) : closure (U ∩ D) = closure U := by
  apply subset_antisymm (closure_mono inter_subset_left)
  exact closure_minimal (hD.open_subset_closure_inter hU) isClosed_closure

variable {m n k : ℕ}

theorem closed_inside_union_of_parity_sum (P : PrePolygon m) (T : PrePolygon n) (Q : PrePolygon k)
    {u : Plane} (hu : Plane.IsDirection u)
    (hP : ∀ R ∈ P.pieces, hgt u R.1 ≠ hgt u R.2)
    (hT : ∀ R ∈ T.pieces, hgt u R.1 ≠ hgt u R.2)
    (hQ : ∀ R ∈ Q.pieces, hgt u R.1 ≠ hgt u R.2)
    (hsum : ∀ x, parity u T.pieces x + parity u Q.pieces x = parity u P.pieces x)
    (hTin : inside T.carrier ⊆ inside P.carrier) :
    closure (inside T.carrier) ∪ closure (inside Q.carrier) = closure (inside P.carrier) := by
  let D := P.carrierᶜ ∩ T.carrierᶜ ∩ Q.carrierᶜ
  have hD : Dense D :=
    ((dense_compl_of_isSeparating P.isSeparating_carrier).inter_of_isOpen_left
      (dense_compl_of_isSeparating T.isSeparating_carrier) P.isClosed_carrier.isOpen_compl).inter_of_isOpen_right
      (dense_compl_of_isSeparating Q.isSeparating_carrier) Q.isClosed_carrier.isOpen_compl
  have he : (inside T.carrier ∪ inside Q.carrier) ∩ D = inside P.carrier ∩ D := by
    ext x
    constructor
    · rintro ⟨hxT | hxQ, hxD⟩
      · exact ⟨hTin hxT, hxD⟩
      · refine ⟨?_, hxD⟩
        by_cases hxT : x ∈ inside T.carrier
        · exact hTin hxT
        have hxTo : x ∈ outside T.carrier := by
          have hx : x ∈ inside T.carrier ∪ outside T.carrier := inside_union_outside T.carrier ▸ hxD.1.2
          exact hx.resolve_left hxT
        have heq := hsum x
        rw [T.parity_eq_zero_of_mem_outside hu hT hxTo,
          Q.parity_eq_one_of_mem_inside hu hQ hxQ, zero_add] at heq
        exact (P.parity_eq_one_iff hu hP hxD.1.1).mp heq.symm
    · rintro ⟨hxP, hxD⟩
      refine ⟨?_, hxD⟩
      by_cases hxT : x ∈ inside T.carrier
      · exact Or.inl hxT
      right
      have hxTo : x ∈ outside T.carrier := by
        have hx : x ∈ inside T.carrier ∪ outside T.carrier := inside_union_outside T.carrier ▸ hxD.1.2
        exact hx.resolve_left hxT
      have heq := hsum x
      rw [T.parity_eq_zero_of_mem_outside hu hT hxTo,
        P.parity_eq_one_of_mem_inside hu hP hxP, zero_add] at heq
      exact (Q.parity_eq_one_iff hu hQ hxD.2).mp heq
  rw [← closure_union, ← closure_inter_dense_of_isOpen
    (T.isSeparating_carrier.isOpen_inside.union Q.isSeparating_carrier.isOpen_inside) hD,
    he, closure_inter_dense_of_isOpen P.isSeparating_carrier.isOpen_inside hD]

theorem disjoint_inside_of_parity_sum (P : PrePolygon m) (T : PrePolygon n) (Q : PrePolygon k)
    {u : Plane} (hu : Plane.IsDirection u)
    (hP : ∀ R ∈ P.pieces, hgt u R.1 ≠ hgt u R.2)
    (hT : ∀ R ∈ T.pieces, hgt u R.1 ≠ hgt u R.2)
    (hQ : ∀ R ∈ Q.pieces, hgt u R.1 ≠ hgt u R.2)
    (hsum : ∀ x, parity u T.pieces x + parity u Q.pieces x = parity u P.pieces x)
    (hTin : inside T.carrier ⊆ inside P.carrier) :
    Disjoint (inside T.carrier) (inside Q.carrier) := by
  refine disjoint_left.mpr ?_
  intro x hxT hxQ
  have heq := hsum x
  rw [T.parity_eq_one_of_mem_inside hu hT hxT, Q.parity_eq_one_of_mem_inside hu hQ hxQ,
    P.parity_eq_one_of_mem_inside hu hP (hTin hxT)] at heq
  exact (by decide : (1 : ZMod 2) + 1 ≠ 1) heq

theorem closed_inside_inter_of_disjoint {C D : Set Plane} (hC : IsSeparating C) (hD : IsSeparating D)
    (hdisj : Disjoint (inside C) (inside D)) :
    closure (inside C) ∩ closure (inside D) = C ∩ D := by
  refine subset_antisymm ?_ ?_
  · rintro x ⟨hxC, hxD⟩
    have hCmem : x ∈ C := by
      rw [(IsRegionOf.inside C).closure_eq hC] at hxC
      exact hxC.resolve_left (fun hx ↦ disjoint_left.mp (hdisj.closure_right hC.isOpen_inside) hx hxD)
    have hDmem : x ∈ D := by
      rw [(IsRegionOf.inside D).closure_eq hD] at hxD
      exact hxD.resolve_left (fun hx ↦ disjoint_left.mp (hdisj.closure_left hD.isOpen_inside) hxC hx)
    exact ⟨hCmem, hDmem⟩
  · rintro x ⟨hxC, hxD⟩
    exact ⟨frontier_subset_closure (hC.frontier_inside.symm ▸ hxC),
      frontier_subset_closure (hD.frontier_inside.symm ▸ hxD)⟩

end Reeken.Geometry
