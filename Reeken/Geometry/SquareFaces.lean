import Reeken.Geometry.PolygonSquareOverlay
import Schoenflies.CrosscutCells

/-! # Faces inside the local square stay on the chosen polygon side -/

open Set Schoenflies

namespace Reeken.Geometry

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {c z : Plane} {r : ℝ}

theorem face_subset_openSquare
    (hS : squareBoundary c r ⊆ Graph.pointSet G drawing)
    (hz : z ∈ Graph.exterior G drawing) (hzin : z ∈ Plane.openSquare c r) :
    Graph.face G drawing z ⊆ Plane.openSquare c r := by
  intro x hx
  by_contra hxo
  have hxr : r ≤ Plane.supDist x c := le_of_not_gt hxo
  obtain ⟨y, hyF, hyS⟩ := exists_square_crossing isPreconnected_connectedComponentIn
    (Graph.mem_face hz) hx (le_of_lt hzin) hxr
  exact (Graph.face_subset_exterior G drawing z hyF) (hS hyS)

/-- Every face lying inside the square has an ordinary uniform norm bound. -/
theorem face_norm_bound
    (hS : squareBoundary c r ⊆ Graph.pointSet G drawing)
    (hz : z ∈ Graph.exterior G drawing) (hzin : z ∈ Plane.openSquare c r) :
    ∀ x ∈ Graph.face G drawing z, ‖x - c‖ ≤ Real.sqrt 2 * r := by
  intro x hx
  exact (Plane.norm_le_sqrt_two_mul_supNorm (x - c)).trans
    (mul_le_mul_of_nonneg_left (face_subset_openSquare hS hz hzin hx).le
      (Real.sqrt_nonneg _))

theorem isBounded_face_of_square
    (hS : squareBoundary c r ⊆ Graph.pointSet G drawing)
    (hz : z ∈ Graph.exterior G drawing) (hzin : z ∈ Plane.openSquare c r) :
    Bornology.IsBounded (Graph.face G drawing z) := by
  apply (isCompact_closedSquare c r).isBounded.subset
  intro x hx
  change Plane.supDist x c ≤ r
  exact le_of_lt (face_subset_openSquare hS hz hzin hx)

theorem face_subset_inside {C : Set Plane} (hC : C ⊆ Graph.pointSet G drawing)
    (hz : z ∈ inside C) : Graph.face G drawing z ⊆ inside C :=
  (connectedComponentIn_mono z (compl_subset_compl.mpr hC)).trans
    (connectedComponentIn_subset_inside hz)

theorem face_subset_outside {C : Set Plane} (hC : C ⊆ Graph.pointSet G drawing)
    (hz : z ∈ outside C) : Graph.face G drawing z ⊆ outside C :=
  (connectedComponentIn_mono z (compl_subset_compl.mpr hC)).trans
    (connectedComponentIn_subset_outside hz)

/-- The boundary of a subset can leave an ambient region only on that region's boundary. -/
theorem frontier_sdiff_frontier_subset {s u : Set Plane} (hsub : s ⊆ u) :
    frontier s \ frontier u ⊆ u := by
  rintro x ⟨hx, hnot⟩
  have hc := closure_mono hsub (frontier_subset_closure hx)
  rw [closure_eq_self_union_frontier] at hc
  exact hc.resolve_right hnot

theorem frontier_face_sdiff_curve_subset_inside {C : Set Plane}
    (hC : C ⊆ Graph.pointSet G drawing) (hsep : IsSeparating C) (hz : z ∈ inside C) :
    frontier (Graph.face G drawing z) \ C ⊆ inside C := by
  simpa only [hsep.frontier_inside] using
    frontier_sdiff_frontier_subset (face_subset_inside hC hz)

theorem frontier_face_sdiff_curve_subset_outside {C : Set Plane}
    (hC : C ⊆ Graph.pointSet G drawing) (hsep : IsSeparating C) (hz : z ∈ outside C) :
    frontier (Graph.face G drawing z) \ C ⊆ outside C := by
  simpa only [hsep.frontier_outside] using
    frontier_sdiff_frontier_subset (face_subset_outside hC hz)

end Reeken.Geometry
