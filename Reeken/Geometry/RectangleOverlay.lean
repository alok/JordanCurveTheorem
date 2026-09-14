import Reeken.Geometry.PolygonFamilyOverlay
import Reeken.Geometry.PolygonRectangles
import Reeken.Geometry.RectangleBoundary
import Reeken.Geometry.BoundaryCrossings

/-! # The finite arrangement of all narrow rectangle boundaries

The rectangles are constructed at their actual edge directions and lengths.
Two separated polygon vertices guarantee that each rectangle boundary crosses
the polygon twice. The whole arrangement therefore has simple polygonal faces.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem exists_rectangle_polygons (hn : 0 < p.n) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin (p.n + 1) → Σ m, ClosedPolygon m,
      ∀ j, (q j).2.carrier = frontier (p.closedRectangle ε j) := by
  classical
  have h : ∀ j : Fin (p.n + 1), ∃ m, ∃ q : ClosedPolygon m,
      q.carrier = frontier (p.closedRectangle ε j) := by
    intro j
    exact exists_closedPolygon
      (isJordanCurve_frontier_closedEdgeRectangle (p.vertex j) (p.edgeDirection_isDirection hn j)
        (show 0 ≤ p.edgeLength j from dist_nonneg) hε)
      (isPolygonal_frontier_closedEdgeRectangle (p.vertex j) (p.edgeDirection_isDirection hn j)
        (show 0 ≤ p.edgeLength j from dist_nonneg) hε)
  choose m q hq using h
  exact ⟨fun j ↦ ⟨m j, q j⟩, hq⟩

theorem Simple.exists_rectangle_overlay (hp : p.Simple) (hn : 2 ≤ p.n) {ε : ℝ} (hε : 0 < ε)
    {a b : Fin (p.n + 1)} (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b)) :
    ∃ q : Fin (p.n + 1) → Σ m, ClosedPolygon m, ∃ points : List Plane,
      (∀ j, (q j).2.carrier = frontier (p.closedRectangle ε j)) ∧
      Graph.IsDrawing (overlayGraph (p.pieces ++ polygonFamilyPieces q) points) segmentDrawing ∧
      (overlayGraph (p.pieces ++ polygonFamilyPieces q) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (p.pieces ++ polygonFamilyPieces q) points) segmentDrawing =
        p.trace ∪ ⋃ j, frontier (p.closedRectangle ε j) ∧
      ∀ i, p.vertex i ∈ V(overlayGraph (p.pieces ++ polygonFamilyPieces q) points) := by
  obtain ⟨q, hq⟩ := p.exists_rectangle_polygons (by omega) hε
  have hC : IsJordanCurve p.trace := by
    rw [← p.toPrePolygon_carrier hn hp]
    exact (p.toPrePolygon hn hp).isJordanCurve_carrier
  have hmeet : ∀ j, ∃ x ∈ p.trace ∩ (q j).2.carrier,
      ∃ y ∈ p.trace ∩ (q j).2.carrier, x ≠ y := by
    intro j
    rw [hq j]
    obtain ⟨k, hk⟩ := p.exists_vertex_outside_rectangle (by omega) hfar j
    exact exists_two_frontier_crossings hC (isClosed_closedEdgeRectangle _ _ _ _)
      (p.vertex_mem_trace j) (p.vertex_mem_trace k)
      (p.openRectangle_subset_interior ε j (p.vertex_mem_openRectangle (by omega) hε j)) hk
  obtain ⟨points, hd, htwo, hpoint, hverts⟩ := hp.exists_family_overlay p hn q hmeet
  exact ⟨q, points, hq, hd, htwo, by simpa only [hq] using hpoint, hverts⟩

end Reeken.Geometry.InscribedPolygon
