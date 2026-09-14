import Reeken.Geometry.InnerFace
import Reeken.Geometry.RectangleSpokes
import Reeken.Geometry.SpokeFeet
import Reeken.Geometry.NearestRegions

/-! # The inner cell with all its corner-to-boundary connections

The arrangement is constructed from the actual covering rectangles and nearest
connections. No separation property of the desired Jordan curve is an input.
Every corner of the chosen inner cell has a shortest connection to the finite
outer polygon that avoids the cell interior. The same uniform error bounds both
the cell's boundary distance and the lengths of these connections.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem Simple.exists_rectangle_spoke_cell (hp : p.Simple) (hn : 2 ≤ p.n)
    {ε : ℝ} (hε : 0 < ε) {a b : Fin (p.n + 1)}
    (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b))
    {z : Plane} (hz : z ∈ inside p.trace)
    (hzR : z ∉ p.rectangleCover ε ∪ p.nearestConnectorCover ε) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m, ∃ foot : Plane → Plane,
      z ∈ inside Q.carrier ∧ Q.carrier ⊆ inside p.trace ∧
      inside Q.carrier ⊆ inside p.trace ∧
      closure (inside Q.carrier) ⊆ (p.openRectangleCover ε)ᶜ ∧
      Q.carrier ⊆ p.rectangleCover ε ∪ p.nearestConnectorCover ε ∧
      (∀ x, IsNearest p.trace x (foot x)) ∧
      ∀ i : ZMod (m + 3),
        Disjoint (segment ℝ (Q.vertex i) (foot (Q.vertex i))) (inside Q.carrier) ∧
        segment ℝ (Q.vertex i) (foot (Q.vertex i)) \ {foot (Q.vertex i)} ⊆ inside p.trace ∧
        dist (Q.vertex i) (foot (Q.vertex i)) ≤ p.maxEdge + 4 * ε := by
  classical
  obtain ⟨q, basePoints, foot, points, hq, hbase, hfoot, hd, htwo, hpoint, hzone, _⟩ :=
    hp.exists_rectangle_spoke_overlay p hn hε hfar
  let base := p.pieces ++ polygonFamilyPieces q
  let G₀ := overlayGraph base basePoints
  let vertices := G₀.vertexFinset
  let G := overlayGraph (vertexSpokePieces base vertices foot) points
  have hbasePoint : Graph.pointSet G₀ segmentDrawing =
      p.trace ∪ ⋃ j, frontier (p.closedRectangle ε j) := by
    change Graph.pointSet (overlayGraph (p.pieces ++ polygonFamilyPieces q) basePoints) _ = _
    rw [overlayGraph_pointSet, cover_append, p.cover_pieces, cover_polygonFamilyPieces]
    simp only [hq]
  have hpoint' : Graph.pointSet G segmentDrawing =
      Graph.pointSet G₀ segmentDrawing ∪ spokeSet vertices foot := by
    rw [hbasePoint]
    exact hpoint
  have hzext : z ∈ Graph.exterior G segmentDrawing := by
    intro h
    exact (hzone h).elim hz.1 hzR
  have hCsub : p.trace ⊆ Graph.pointSet G segmentDrawing := by
    rw [hpoint]
    exact fun x hx ↦ Or.inl (Or.inl hx)
  have hboundary : ∀ j, frontier (p.closedRectangle ε j) ⊆ Graph.pointSet G segmentDrawing := by
    intro j x hx
    rw [hpoint]
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j, hx⟩))
  have hcover : p.trace ⊆ p.openRectangleCover ε := by
    intro x hx
    exact p.mem_openRectangleCover_of_near_trace (by omega) hε hx (by simpa using hε.le)
  obtain ⟨m, Q, hzQ, hQin, hin, hclosure, hQsub, hface⟩ := exists_inner_face_polygon hd
    (fun e _ ↦ by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _) htwo
    (hp.isSeparating hn) hCsub (fun j ↦ isClosed_closedEdgeRectangle _ _ _ _)
    hboundary (p.openRectangle_subset_interior ε) hcover hz hzext
    (fun j hj ↦ hzR (Or.inl (mem_iUnion.mpr ⟨j, hj⟩)))
  have hQzone : Q.carrier ⊆ p.rectangleCover ε ∪ p.nearestConnectorCover ε := by
    intro x hx
    exact (hzone (hQsub hx)).resolve_left (hQin hx).1
  have hspoke : ∀ i : ZMod (m + 3),
      segment ℝ (Q.vertex i) (foot (Q.vertex i)) ⊆ Graph.pointSet G segmentDrawing := by
    intro i
    have hQsub' : Q.carrier ⊆ Graph.pointSet G₀ segmentDrawing ∪ spokeSet vertices foot :=
      hpoint' ▸ hQsub
    have h := polygon_vertex_nearest_segment_subset_spokes hbase
      (fun x hx ↦ Graph.mem_vertexFinset.mpr hx) hfoot Q hQsub' i
    exact fun x hx ↦ hpoint'.symm ▸ Or.inr (h hx)
  refine ⟨m, Q, foot, hzQ, hQin, hin, hclosure, hQzone, hfoot, fun i ↦ ?_⟩
  refine ⟨?_, (hfoot (Q.vertex i)).segment_sdiff_subset_region (hp.isSeparating hn)
    (Or.inl rfl) (hQin Q.vertex_mem_carrier), ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hxQ
    rw [hface] at hxQ
    exact Graph.face_subset_exterior G segmentDrawing z hxQ (hspoke i hx)
  · have hnear : ∃ y ∈ p.trace, dist (Q.vertex i) y ≤ p.maxEdge + 4 * ε := by
      rcases hQzone Q.vertex_mem_carrier with hi | hi
      · exact p.rectangleCover_near_trace (by omega) hi
      · exact p.nearestConnectorCover_near_trace (by omega) hi
    obtain ⟨y, hy, hdist⟩ := hnear
    exact ((hfoot (Q.vertex i)).2 y hy).trans hdist

end Reeken.Geometry.InscribedPolygon
