import Reeken.Geometry.RectangleOverlay
import Reeken.Geometry.NearestSpokeDrawing

/-! # The rectangle arrangement with its shortest boundary connections

Draw a nearest connection from every vertex of the subdivided rectangle overlay.
All rectangle corners and all crossings in that drawing are therefore included.
The new carrier remains in the controlled rectangle-and-connection zone.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem Simple.exists_rectangle_spoke_overlay (hp : p.Simple) (hn : 2 ≤ p.n) {ε : ℝ} (hε : 0 < ε)
    {a b : Fin (p.n + 1)} (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b)) :
    ∃ q : Fin (p.n + 1) → Σ m, ClosedPolygon m, ∃ basePoints : List Plane,
      ∃ foot : Plane → Plane, ∃ points : List Plane,
      let base := p.pieces ++ polygonFamilyPieces q
      let vertices := (overlayGraph base basePoints).vertexFinset
      let G := overlayGraph (vertexSpokePieces base vertices foot) points
      (∀ j, (q j).2.carrier = frontier (p.closedRectangle ε j)) ∧
      Graph.IsDrawing (overlayGraph base basePoints) segmentDrawing ∧
      (∀ x, IsNearest p.trace x (foot x)) ∧
      Graph.IsDrawing G segmentDrawing ∧ G.IsTwoConnected ∧
      Graph.pointSet G segmentDrawing =
        (p.trace ∪ ⋃ j, frontier (p.closedRectangle ε j)) ∪
          ⋃ x ∈ vertices, segment ℝ x (foot x) ∧
      Graph.pointSet G segmentDrawing ⊆
        p.trace ∪ (p.rectangleCover ε ∪ p.nearestConnectorCover ε) ∧
      ∀ x ∈ vertices, segment ℝ x (foot x) ⊆ Graph.pointSet G segmentDrawing := by
  classical
  obtain ⟨q, basePoints, hq, hbaseDraw, hbaseTwo, _, _⟩ := hp.exists_rectangle_overlay p hn hε hfar
  let base := p.pieces ++ polygonFamilyPieces q
  let G₀ := overlayGraph base basePoints
  have hcover : cover base = p.trace ∪ ⋃ j, (q j).2.carrier := by
    change cover (p.pieces ++ polygonFamilyPieces q) = _
    rw [cover_append, p.cover_pieces, cover_polygonFamilyPieces]
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
  have hconn : IsPreconnected (cover base) := by
    rw [hcover]
    exact isPreconnected_curve_union_family hC.isConnected
      (fun j ↦ (q j).2.isJordanCurve_carrier.isConnected.isPreconnected)
      (fun j ↦ ⟨(hmeet j).choose, (hmeet j).choose_spec.1⟩)
  have hpunctured : ∀ z, IsPreconnected (cover base \ {z}) := by
    intro z
    rw [hcover]
    exact isPreconnected_punctured_family hC (fun j ↦ (q j).2.isJordanCurve_carrier) hmeet z
  have hnd : ∀ P ∈ base, P.Nondeg := by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact p.pieces_nondeg (by omega) P hP
    · exact polygonFamilyPieces_nondeg q P hP
  have hverts : (G₀.vertexFinset : Set Plane) ⊆ cover base := by
    intro x hx
    have hxP : x ∈ Graph.pointSet G₀ segmentDrawing := Or.inl (Graph.mem_vertexFinset.mp hx)
    rwa [overlayGraph_pointSet] at hxP
  have hCsub : p.trace ⊆ cover base := by rw [hcover]; exact subset_union_left
  obtain ⟨x, hx, y, hy, w, hw, hxy, hxw, hyw⟩ := hbaseTwo.1
  obtain ⟨foot, points, hfoot, hd, htwo, hpoint, _⟩ := exists_nearest_spoke_drawing base G₀.vertexFinset
    hnd hconn hpunctured hverts p.isCompact_trace p.trace_nonempty hCsub
    (Graph.mem_vertexFinset.mpr hx) (Graph.mem_vertexFinset.mpr hy) (Graph.mem_vertexFinset.mpr hw)
    hxy hxw hyw
  have hpoint' : Graph.pointSet
      (overlayGraph (vertexSpokePieces base G₀.vertexFinset foot) points) segmentDrawing =
      (p.trace ∪ ⋃ j, frontier (p.closedRectangle ε j)) ∪
        ⋃ x ∈ G₀.vertexFinset, segment ℝ x (foot x) := by
    simpa only [hcover, hq] using hpoint
  refine ⟨q, basePoints, foot, points, hq, hbaseDraw, hfoot, hd, htwo, hpoint', ?_, ?_⟩
  · intro z hz
    rw [hpoint] at hz
    rcases hz with hzBase | hzSpoke
    · rw [hcover] at hzBase
      rcases hzBase with hzC | hzRect
      · exact Or.inl hzC
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hzRect
        rw [hq j] at hj
        exact Or.inr (Or.inl (mem_iUnion.mpr
          ⟨j, (isClosed_closedEdgeRectangle _ _ _ _).frontier_subset hj⟩))
    · obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzSpoke
      have hvBase := hverts hv
      rw [hcover] at hvBase
      rcases hvBase with hvC | hvRect
      · have hf : foot v = v := by
          have h := (hfoot v).2 v hvC
          rw [dist_self] at h
          exact (dist_le_zero.mp h).symm
        have hzv' : z = v := by simpa only [hf, segment_same, mem_singleton_iff] using hzv
        exact Or.inl (hzv' ▸ hvC)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hvRect
        rw [hq j] at hj
        exact Or.inr (Or.inr ⟨v, mem_iUnion.mpr
          ⟨j, (isClosed_closedEdgeRectangle _ _ _ _).frontier_subset hj⟩, foot v, hfoot v, hzv⟩)
  · intro v hv z hz
    rw [hpoint']
    exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, hz⟩)

end Reeken.Geometry.InscribedPolygon
