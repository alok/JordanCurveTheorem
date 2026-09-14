import Reeken.Geometry.MarkedOverlay
import Reeken.Geometry.SquareCrossings
import Schoenflies.SquarePieces

/-! # The finite graph formed by a polygon and a local square

The overlay is constructed by cutting the original segments at all intersections,
the original polygon vertices, and two distinct arc-square crossings. Its carrier
is exactly the polygon together with the square boundary.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

noncomputable def pieces : List Piece :=
  List.ofFn fun i ↦ (p.vertex i, p.vertex (nextIndex p.n i))

theorem cover_pieces : cover p.pieces = p.trace := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact mem_iUnion.mpr ⟨i, hxP⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

theorem pieces_nondeg (hn : 0 < p.n) : ∀ P ∈ p.pieces, P.Nondeg := by
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  exact fun h ↦ nextIndex_ne_self hn i (p.vertex_injective h).symm

noncomputable def squareOverlayPieces (c : Plane) (r : ℝ) : List Piece :=
  p.pieces ++ squarePieces c r

theorem cover_squareOverlayPieces (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    cover (p.squareOverlayPieces c r) = p.trace ∪ squareBoundary c r := by
  rw [squareOverlayPieces, cover_append, p.cover_pieces, cover_squarePieces c hr,
    Plane.frontier_closedSquare]
  rfl

theorem squareOverlayPieces_nondeg (hn : 0 < p.n) (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∀ P ∈ p.squareOverlayPieces c r, P.Nondeg := by
  intro P hP
  rcases List.mem_append.mp hP with hP | hP
  · exact p.pieces_nondeg hn P hP
  · exact squarePieces_nondeg c hr P hP

/-- The local square and polygon have an actual finite plane drawing with all old
vertices retained and two distinct common vertices, one on each cut arc. -/
theorem Simple.exists_square_overlay (hp : p.Simple) (hn : 0 < p.n)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) {c : Plane} {r : ℝ} (hr : 0 < r)
    (ha : p.vertex a ∈ Plane.openSquare c r)
    (hb : p.vertex b ∉ Plane.closedSquare c r) :
    ∃ points : List Plane,
      EndsAreCut (p.squareOverlayPieces c r) points ∧
      MeetsAreCut (p.squareOverlayPieces c r) points ∧
      Graph.IsDrawing (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing ∧
      Graph.pointSet (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing =
        p.trace ∪ squareBoundary c r ∧
      (∀ i, p.vertex i ∈ V(overlayGraph (p.squareOverlayPieces c r) points)) ∧
      ∃ x ∈ p.forwardArc a b ∩ squareBoundary c r,
        ∃ y ∈ p.backwardArc a b ∩ squareBoundary c r, x ≠ y ∧
          x ∈ V(overlayGraph (p.squareOverlayPieces c r) points) ∧
          y ∈ V(overlayGraph (p.squareOverlayPieces c r) points) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hp.exists_distinct_square_crossings hab ha hb
  let marked := List.ofFn p.vertex ++ [x, y]
  obtain ⟨points, hmarked, hEnds, hMeets⟩ :=
    exists_marked_cut_points (p.squareOverlayPieces c r) marked
  have hnd := p.squareOverlayPieces_nondeg hn c hr
  have hvertex : ∀ z ∈ marked, z ∈ p.trace ∪ squareBoundary c r →
      z ∈ V(overlayGraph (p.squareOverlayPieces c r) points) := by
    intro z hz hcover
    apply mem_overlay_vertex_of_cut hnd (hmarked hz)
    rwa [p.cover_squareOverlayPieces c hr.le]
  refine ⟨points, hEnds, hMeets,
    overlayGraph_isDrawing _ _ hnd hEnds hMeets, ?_, ?_, x, hx, y, hy, hxy, ?_, ?_⟩
  · rw [overlayGraph_pointSet, p.cover_squareOverlayPieces c hr.le]
  · intro i
    exact hvertex _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
      (Or.inl (p.vertex_mem_trace i))
  · exact hvertex x (by simp [marked]) (Or.inr hx.2)
  · exact hvertex y (by simp [marked]) (Or.inr hy.2)

end Reeken.Geometry.InscribedPolygon
