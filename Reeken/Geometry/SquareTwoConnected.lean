import Reeken.Geometry.DrawingDeletion
import Reeken.Geometry.LoopPuncture
import Reeken.Geometry.SquareConnectivity
import Reeken.Geometry.PolygonSeparation
import Schoenflies.SquarePolygon

/-! # The polygon-square overlay remains connected after deleting any vertex

Each of the two simple closed carriers remains connected when punctured. Their
two distinct common points guarantee a surviving common point after one deletion.
The geometric deletion criterion then gives the finite graph's 2-connectivity.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem isPreconnected_punctured_union {C D : Set Plane}
    (hC : ∀ z, IsPreconnected (C \ {z})) (hD : ∀ z, IsPreconnected (D \ {z}))
    {x y : Plane} (hx : x ∈ C ∩ D) (hy : y ∈ C ∩ D) (hxy : x ≠ y) (z : Plane) :
    IsPreconnected ((C ∪ D) \ {z}) := by
  obtain ⟨w, hwC, hwD, hwz⟩ : ∃ w, w ∈ C ∧ w ∈ D ∧ w ≠ z := by
    by_cases hxz : x = z
    · exact ⟨y, hy.1, hy.2, fun hyz ↦ hxy (hxz.trans hyz.symm)⟩
    · exact ⟨x, hx.1, hx.2, hxz⟩
  rw [union_sdiff_distrib]
  exact IsPreconnected.union w ⟨hwC, hwz⟩ ⟨hwD, hwz⟩ (hC z) (hD z)

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem Simple.square_overlay_isTwoConnected (hp : p.Simple) (hn : 2 ≤ p.n)
    {c : Plane} {r : ℝ} (hr : 0 < r) (points : List Plane)
    (hd : Graph.IsDrawing (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing)
    (hverts : ∀ i, p.vertex i ∈ V(overlayGraph (p.squareOverlayPieces c r) points))
    {x y : Plane} (hx : x ∈ p.trace ∩ squareBoundary c r)
    (hy : y ∈ p.trace ∩ squareBoundary c r) (hxy : x ≠ y) :
    (overlayGraph (p.squareOverlayPieces c r) points).IsTwoConnected := by
  have hthree : (overlayGraph (p.squareOverlayPieces c r) points).HasThreeVertices := by
    refine ⟨p.vertex ⟨0, by omega⟩, hverts _, p.vertex ⟨1, by omega⟩, hverts _,
      p.vertex ⟨2, by omega⟩, hverts _, ?_, ?_, ?_⟩
    all_goals
      apply p.vertex_injective.ne
      exact fun he ↦ by have := congrArg Fin.val he; norm_num at this
  have hpoly : IsJordanCurve p.trace := by
    rw [← p.toPrePolygon_carrier hn hp]
    exact (p.toPrePolygon hn hp).isJordanCurve_carrier
  have hsq : IsJordanCurve (squareBoundary c r) := by
    change IsJordanCurve {z | Plane.supDist z c = r}
    rw [← Plane.frontier_closedSquare]
    exact isJordanCurve_frontier_closedSquare c hr
  refine ⟨hthree, p.square_overlay_connected hr.le points hd ⟨x, hx⟩, ?_⟩
  intro z _
  apply connected_deleteVerts_of_punctured hd z
  · rw [overlayGraph_pointSet, p.cover_squareOverlayPieces c hr.le]
    exact isPreconnected_punctured_union (isPreconnected_punctured_jordan hpoly)
      (isPreconnected_punctured_jordan hsq) hx hy hxy z
  · obtain ⟨w, hw, hwz, _⟩ := hthree.exists_ne_ne z z
    exact ⟨w, hw, hwz⟩

/-- The actual local construction produces a finite 2-connected plane graph. -/
theorem Simple.exists_twoConnected_square_overlay (hp : p.Simple) (hn : 2 ≤ p.n)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) {c : Plane} {r : ℝ} (hr : 0 < r)
    (ha : p.vertex a ∈ Plane.openSquare c r)
    (hb : p.vertex b ∉ Plane.closedSquare c r) :
    ∃ points : List Plane,
      Graph.IsDrawing (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing ∧
      (overlayGraph (p.squareOverlayPieces c r) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (p.squareOverlayPieces c r) points) segmentDrawing =
        p.trace ∪ squareBoundary c r ∧
      (∀ i, p.vertex i ∈ V(overlayGraph (p.squareOverlayPieces c r) points)) := by
  obtain ⟨points, _, _, hd, he, hv, x, hx, y, hy, hxy, _, _⟩ :=
    hp.exists_square_overlay p (by omega) hab hr ha hb
  have hx' : x ∈ p.trace ∩ squareBoundary c r := by
    rw [← p.arcs_union a b]
    exact ⟨Or.inl hx.1, hx.2⟩
  have hy' : y ∈ p.trace ∩ squareBoundary c r := by
    rw [← p.arcs_union a b]
    exact ⟨Or.inr hy.1, hy.2⟩
  exact ⟨points, hd, hp.square_overlay_isTwoConnected p hn hr points hd hv hx' hy' hxy, he, hv⟩

end InscribedPolygon
end Reeken.Geometry
