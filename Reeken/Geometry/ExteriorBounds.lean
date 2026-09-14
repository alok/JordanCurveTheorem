import Schoenflies.Bounded
import Schoenflies.CrosscutCells

/-! # Uniform bounds for polygon interiors and exteriors

A connected unbounded set outside an enclosing square belongs to an unbounded
complementary component. This needs no Jordan theorem.
-/

open Set Metric
open Schoenflies

namespace Reeken.Geometry

theorem not_isBounded_beyondSquare (r : ℝ) :
    ¬ Bornology.IsBounded (Plane.beyondSquare r) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  let x := Plane.mk (max r R + 1) 0
  have hx : x ∈ Plane.beyondSquare r := by
    left
    change r < |max r R + 1|
    exact ((le_max_left r R).trans_lt (lt_add_one (max r R))).trans_le (le_abs_self _)
  have hcoord : |x 0| ≤ ‖x‖ := (le_max_left _ _).trans (Plane.supNorm_le_norm x)
  have hxR := hR x hx
  have hle : max r R + 1 ≤ R := (le_abs_self _).trans (hcoord.trans hxR)
  linarith [le_max_right r R]

theorem beyondSquare_subset_outside {C : Set Plane} {r : ℝ}
    (hC : C ⊆ Plane.closedSquare 0 r) : Plane.beyondSquare r ⊆ outside C := by
  have hsub : Plane.beyondSquare r ⊆ Cᶜ := by
    rw [Plane.beyondSquare_eq_compl]
    exact compl_subset_compl.mpr hC
  intro x hx
  refine ⟨hsub hx, fun hb ↦ not_isBounded_beyondSquare r ?_⟩
  exact hb.subset ((Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
    hx hsub)

theorem inside_subset_closedSquare {C : Set Plane} {r : ℝ}
    (hC : C ⊆ Plane.closedSquare 0 r) : inside C ⊆ Plane.closedSquare 0 r := by
  intro x hx
  by_contra hn
  have hb : x ∈ Plane.beyondSquare r := by
    rwa [Plane.beyondSquare_eq_compl]
  have ho := beyondSquare_subset_outside hC hb
  exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hx ho

end Reeken.Geometry
