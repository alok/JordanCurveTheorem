import Schoenflies.ParitySplitting

/-! # Crossing parity after closing each edge against a boundary arc

For each edge of a closed chain, join its ends to two boundary points and close
it by an arc between those points. Summing the small closed barriers cancels the
endpoint connections in pairs. The remaining boundary-arc chain is closed.
This is the finite parity calculation behind the ring separation argument.
-/

open Set Schoenflies

namespace Reeken.Geometry

def edgeBarrier (foot : Plane → Plane) (arc : Piece → List Piece) (P : Piece) : List Piece :=
  [P, (P.2, foot P.2), (foot P.1, P.1)] ++ arc P

theorem isClosedChain_edgeBarrier {foot : Plane → Plane} {arc : Piece → List Piece} {P : Piece}
    (h : IsChainFrom (arc P) (foot P.1) (foot P.2)) :
    IsClosedChain (edgeBarrier foot arc P) := by
  intro f
  simp only [edgeBarrier, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [h f]
  linear_combination add_self_zmod_two (f P.1) + add_self_zmod_two (f P.2) +
    add_self_zmod_two (f (foot P.1)) + add_self_zmod_two (f (foot P.2))

theorem isClosedChain_replacement_arcs {L : List Piece} (hL : IsClosedChain L)
    {foot : Plane → Plane} {arc : Piece → List Piece}
    (h : ∀ P ∈ L, IsChainFrom (arc P) (foot P.1) (foot P.2)) :
    IsClosedChain (L.flatMap arc) := by
  intro f
  have heq : ((L.flatMap arc).map fun P ↦ f P.1 + f P.2).sum =
      (L.map fun P ↦ f (foot P.1) + f (foot P.2)).sum := by
    clear hL
    induction L with
    | nil => rfl
    | cons P L ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [h P (by simp), ih (fun R hR ↦ h R (by simp [hR]))]
  rw [heq]
  exact hL (fun x ↦ f (foot x))

/-- Each endpoint connection occurs with the mod-two multiplicity of that vertex
in the original chain boundary, which is zero. -/
theorem parity_edge_barriers {L : List Piece} (hL : IsClosedChain L)
    (foot : Plane → Plane) (arc : Piece → List Piece) (u x : Plane) :
    parity u (L.flatMap (edgeBarrier foot arc)) x =
      parity u L x + parity u (L.flatMap arc) x := by
  let g : Plane → ZMod 2 := fun z ↦ mark u (z, foot z) x
  have heq : ∀ M : List Piece,
      parity u (M.flatMap (edgeBarrier foot arc)) x =
        parity u M x + parity u (M.flatMap arc) x +
          (M.map fun P ↦ g P.1 + g P.2).sum := by
    intro M
    induction M with
    | nil => simp
    | cons P M ih =>
      simp only [List.flatMap_cons, parity_append, edgeBarrier, parity_cons, parity_nil,
        List.map_cons, List.sum_cons, ih]
      rw [mark_swap' u (P.1, foot P.1) x]
      change _ = _ + _ + ((mark u (P.1, foot P.1) x + mark u (P.2, foot P.2) x) + _)
      abel
  rw [heq, hL g, add_zero]

theorem parity_eq_of_edge_barriers {L : List Piece} (hL : IsClosedChain L)
    (foot : Plane → Plane) (arc : Piece → List Piece) {u x y : Plane}
    (hbarriers : ∀ P ∈ L, parity u (edgeBarrier foot arc P) x = parity u (edgeBarrier foot arc P) y)
    (harcs : parity u (L.flatMap arc) x = parity u (L.flatMap arc) y) :
    parity u L x = parity u L y := by
  have hsum_aux : ∀ M : List Piece,
      (∀ P ∈ M, parity u (edgeBarrier foot arc P) x = parity u (edgeBarrier foot arc P) y) →
      parity u (M.flatMap (edgeBarrier foot arc)) x =
        parity u (M.flatMap (edgeBarrier foot arc)) y := by
    intro M hM
    induction M with
    | nil => rfl
    | cons P M ih =>
      simp only [List.flatMap_cons, parity_append]
      rw [hM P (by simp)]
      congr 1
      exact ih (fun R hR ↦ hM R (by simp [hR]))
  have hsum := hsum_aux L hbarriers
  rw [parity_edge_barriers hL foot arc, parity_edge_barriers hL foot arc, harcs] at hsum
  exact add_right_cancel hsum

end Reeken.Geometry
