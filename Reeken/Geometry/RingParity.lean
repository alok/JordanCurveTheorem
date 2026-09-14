import Reeken.Geometry.EdgeReplacementParity
import Reeken.Geometry.SmallChainParity

/-! # The separation step for the inner polygon

If every edge barrier gives the same crossing parity at two points inside the
outer polygon, the inner polygon does too. The boundary-arc chain left after
the connections cancel lies on the outer polygon, so its parity is constant
throughout that polygon's connected inside.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem parity_eq_inside_of_edge_barriers {L : List Piece} (hclosed : IsClosedChain L)
    (foot : Plane → Plane) (arc : Piece → List Piece)
    (hchain : ∀ P ∈ L, IsChainFrom (arc P) (foot P.1) (foot P.2))
    {C : Set Plane} (hC : IsSeparating C) (hcover : ∀ P ∈ L, cover (arc P) ⊆ C)
    {u : Plane} (hu : Plane.IsDirection u)
    (hdir : ∀ P ∈ L.flatMap arc, P.Nondeg → hgt u P.1 ≠ hgt u P.2)
    {x y : Plane} (hx : x ∈ inside C) (hy : y ∈ inside C)
    (hbarriers : ∀ P ∈ L,
      parity u (edgeBarrier foot arc P) x = parity u (edgeBarrier foot arc P) y) :
    parity u L x = parity u L y := by
  apply parity_eq_of_edge_barriers hclosed foot arc hbarriers
  apply parity_eq_on_preconnected_complement (isClosedChain_replacement_arcs hclosed hchain)
    hu hdir hC.isConnected_inside.isPreconnected _ hx hy
  rw [Set.disjoint_left, cover_flatMap]
  intro z hz hzArc
  obtain ⟨P, hP, hzP⟩ := mem_iUnion₂.mp hzArc
  exact hz.1 (hcover P hP hzP)

end Reeken.Geometry
