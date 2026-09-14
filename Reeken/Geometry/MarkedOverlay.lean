import Schoenflies.OverlayGraph

/-! # Subdividing at prescribed points as well as segment intersections -/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

/-- Additional prescribed points can be included in the finite subdivision. -/
theorem exists_marked_cut_points (pieces : List Piece) (marked : List Plane) :
    ∃ points : List Plane, marked ⊆ points ∧
      EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  obtain ⟨points, hEnds, hMeets⟩ := exists_cut_points pieces
  refine ⟨marked ++ points, List.subset_append_left _ _,  ?_, ?_⟩
  · exact fun P hP z hz ↦ List.mem_append_right _ (hEnds P hP z hz)
  · intro P hP Q hQ hPQ hne
    obtain ⟨u, v, he, hu, hv⟩ := hMeets P hP Q hQ hPQ hne
    exact ⟨u, v, he, List.mem_append_right _ hu, List.mem_append_right _ hv⟩

/-- A cut point on the carrier is an actual graph vertex, not merely a point on an edge. -/
theorem mem_overlay_vertex_of_cut {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hx : x ∈ points)
    (hcover : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hcover
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hcover
  refine ⟨P, hP, ?_⟩
  by_contra h
  push Not at h
  exact overlayPieces_avoids hnd x hx P hP
    (mem_openSegment_of_ne_left_right h.1.symm h.2.symm hxP)

end Reeken.Geometry
