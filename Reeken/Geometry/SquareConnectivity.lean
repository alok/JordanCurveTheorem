import Reeken.Geometry.PolygonSquareOverlay
import Schoenflies.Graph.Trace

/-! # Connectivity of the polygon-square overlay -/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem isPathConnected_squareBoundary (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (squareBoundary c r) := by
  have hs (a b : Plane) : IsPathConnected (segment ℝ a b) :=
    (convex_segment a b).isPathConnected ⟨_, left_mem_segment ℝ _ _⟩
  have h12 := (hs (Plane.sqNE c r) (Plane.sqNW c r)).union
    (hs (Plane.sqNW c r) (Plane.sqSW c r))
    ⟨Plane.sqNW c r, right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have h123 := h12.union (hs (Plane.sqSW c r) (Plane.sqSE c r))
    ⟨Plane.sqSW c r, Or.inr (right_mem_segment ℝ _ _), left_mem_segment ℝ _ _⟩
  have h := h123.union (hs (Plane.sqSE c r) (Plane.sqNE c r))
    ⟨Plane.sqSE c r, Or.inr (right_mem_segment ℝ _ _), left_mem_segment ℝ _ _⟩
  have he : squareBoundary c r = cover (squarePieces c r) := by
    rw [cover_squarePieces c hr, Plane.frontier_closedSquare]
    rfl
  rw [he]
  simpa only [squarePieces, cover_cons, cover_nil, union_empty, Piece.seg, union_assoc] using h

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem square_overlay_connected {c : Plane} {r : ℝ} (hr : 0 ≤ r)
    (points : List Plane)
    (hd : Graph.IsDrawing (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing)
    (hmeet : (p.trace ∩ squareBoundary c r).Nonempty) :
    (overlayGraph (p.squareOverlayPieces c r) points).Connected := by
  have he : Graph.pointSet (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing =
      p.trace ∪ squareBoundary c r := by
    rw [overlayGraph_pointSet, p.cover_squareOverlayPieces c hr]
  apply Graph.connected_of_isPreconnected_pointSet hd
  · rw [he]
    exact (p.isPathConnected_trace.union (isPathConnected_squareBoundary c hr) hmeet).isConnected.isPreconnected
  · have hv : p.vertex 0 ∈ Graph.pointSet
        (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing := by
      rw [he]
      exact Or.inl (p.vertex_mem_trace 0)
    rcases hv with hv | hv
    · exact ⟨_, hv⟩
    · obtain ⟨e, he, _⟩ := mem_iUnion₂.mp hv
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
      exact ⟨a, hab.left_mem⟩

end InscribedPolygon
end Reeken.Geometry
