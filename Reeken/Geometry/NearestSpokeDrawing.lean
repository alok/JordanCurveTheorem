import Reeken.Geometry.AttachedSegments
import Reeken.Geometry.NearestRegions

/-! # Drawing shortest boundary connections from a finite set of arrangement vertices -/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

noncomputable def vertexSpokePieces (pieces : List Piece) (vertices : Finset Plane)
    (foot : Plane → Plane) : List Piece :=
  attachedPieces pieces (fun v : vertices ↦ (v : Plane)) (fun v ↦ foot (v : Plane))

/-- All selected shortest connections are constructed and included in a finite
2-connected drawing, even when feet coincide or some connections are degenerate. -/
theorem exists_nearest_spoke_drawing (pieces : List Piece) (vertices : Finset Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hconn : IsPreconnected (cover pieces))
    (hpunctured : ∀ z, IsPreconnected (cover pieces \ {z}))
    (hvertices : (vertices : Set Plane) ⊆ cover pieces)
    {C : Set Plane} (hC : IsCompact C) (hCne : C.Nonempty) (hCsub : C ⊆ cover pieces)
    {x y w : Plane} (hx : x ∈ vertices) (hy : y ∈ vertices) (hw : w ∈ vertices)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ foot : Plane → Plane, ∃ points : List Plane,
      (∀ z, IsNearest C z (foot z)) ∧
      Graph.IsDrawing (overlayGraph (vertexSpokePieces pieces vertices foot) points) segmentDrawing ∧
      (overlayGraph (vertexSpokePieces pieces vertices foot) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (vertexSpokePieces pieces vertices foot) points) segmentDrawing =
        cover pieces ∪ ⋃ z ∈ vertices, segment ℝ z (foot z) ∧
      ∀ z ∈ vertices, z ∈ V(overlayGraph (vertexSpokePieces pieces vertices foot) points) := by
  classical
  choose foot hfoot using fun z : Plane ↦ exists_nearest_of_isCompact hC hCne z
  have : Nonempty vertices := ⟨⟨x, hx⟩⟩
  obtain ⟨points, _, hd, htwo, hpoint, hmarked⟩ := exists_attached_segments_overlay pieces hnd
    hconn hpunctured (fun v : vertices ↦ (v : Plane)) (fun v ↦ foot (v : Plane))
    (fun v ↦ hvertices v.property) (fun v ↦ hCsub (hfoot v).1)
    (hvertices hx) (hvertices hy) (hvertices hw) hxy hxw hyw vertices.toList
  refine ⟨foot, points, hfoot, hd, htwo, ?_, ?_⟩
  · have he : (⋃ v : vertices, segment ℝ (v : Plane) (foot v)) =
        ⋃ z ∈ vertices, segment ℝ z (foot z) := by
      ext z
      simp
    simpa only [vertexSpokePieces, he] using hpoint
  · intro z hz
    exact hmarked z (by simpa using hz) (hvertices hz)

end Reeken.Geometry
