import Reeken.Geometry.AnnulusConnectivity
import Reeken.Geometry.AttachedSegments
import Reeken.Geometry.PolygonSeparation
import Reeken.Geometry.PolygonSquareOverlay

/-! # The finite drawing of the two polygons and their nearest connections

Two disjoint connections make the ring drawing 2-connected. The graph is built
by subdividing the actual finite segment family, retaining both polygons' vertices.
Its bounded faces therefore have simple polygon boundaries.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

noncomputable def annulusPieces {m : ℕ} (Q : ClosedPolygon m) (foot : Plane → Plane) : List Piece :=
  attachedPieces (p.pieces ++ Q.pieces) Q.vertex (fun j ↦ foot (Q.vertex j))

theorem cover_annulusPieces {m : ℕ} (Q : ClosedPolygon m) (foot : Plane → Plane) :
    cover (p.annulusPieces Q foot) = (p.trace ∪ Q.carrier) ∪
      ⋃ j, segment ℝ (Q.vertex j) (foot (Q.vertex j)) := by
  rw [annulusPieces, cover_attachedPieces]
  · rw [cover_append, p.cover_pieces, Q.cover_pieces]
  · intro j
    rw [cover_append, Q.cover_pieces]
    exact Or.inr Q.vertex_mem_carrier

theorem Simple.exists_annulus_overlay (hp : p.Simple) (hn : 2 ≤ p.n)
    {m : ℕ} (Q : ClosedPolygon m) (foot : Plane → Plane)
    (hfoot : ∀ j, foot (Q.vertex j) ∈ p.trace) {j k : ZMod (m + 3)}
    (hdis : Disjoint (segment ℝ (Q.vertex j) (foot (Q.vertex j)))
      (segment ℝ (Q.vertex k) (foot (Q.vertex k)))) :
    ∃ points : List Plane,
      Graph.IsDrawing (overlayGraph (p.annulusPieces Q foot) points) segmentDrawing ∧
      (overlayGraph (p.annulusPieces Q foot) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (p.annulusPieces Q foot) points) segmentDrawing =
        (p.trace ∪ Q.carrier) ∪ ⋃ j, segment ℝ (Q.vertex j) (foot (Q.vertex j)) ∧
      (∀ i, p.vertex i ∈ V(overlayGraph (p.annulusPieces Q foot) points)) ∧
      ∀ i, Q.vertex i ∈ V(overlayGraph (p.annulusPieces Q foot) points) := by
  classical
  have hnd : ∀ P ∈ p.annulusPieces Q foot, P.Nondeg := by
    apply attachedPieces_nondeg
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact p.pieces_nondeg (by omega) P hP
    · exact Q.pieces_nondeg P hP
  obtain ⟨points, hmarked, hEnds, hMeets⟩ := exists_marked_cut_points (p.annulusPieces Q foot)
    (List.ofFn p.vertex ++ (Finset.univ.toList.map Q.vertex))
  have hd := overlayGraph_isDrawing _ points hnd hEnds hMeets
  have hpoint : Graph.pointSet (overlayGraph (p.annulusPieces Q foot) points) segmentDrawing =
      (p.trace ∪ Q.carrier) ∪ ⋃ j, segment ℝ (Q.vertex j) (foot (Q.vertex j)) := by
    rw [overlayGraph_pointSet, p.cover_annulusPieces]
  have hverts : ∀ i, p.vertex i ∈ V(overlayGraph (p.annulusPieces Q foot) points) := by
    intro i
    apply mem_overlay_vertex_of_cut hnd (hmarked (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    rw [p.cover_annulusPieces]
    exact Or.inl (Or.inl (p.vertex_mem_trace i))
  have hQverts : ∀ i, Q.vertex i ∈ V(overlayGraph (p.annulusPieces Q foot) points) := by
    intro i
    have hmem : Q.vertex i ∈ List.ofFn p.vertex ++ Finset.univ.toList.map Q.vertex :=
      List.mem_append_right _ (List.mem_map.mpr ⟨i, by simp, rfl⟩)
    apply mem_overlay_vertex_of_cut hnd (hmarked hmem)
    rw [p.cover_annulusPieces]
    exact Or.inl (Or.inr Q.vertex_mem_carrier)
  have hthree : (overlayGraph (p.annulusPieces Q foot) points).HasThreeVertices := by
    refine ⟨p.vertex ⟨0, by omega⟩, hverts _, p.vertex ⟨1, by omega⟩, hverts _,
      p.vertex ⟨2, by omega⟩, hverts _, ?_, ?_, ?_⟩
    all_goals
      apply p.vertex_injective.ne
      exact fun he ↦ by have := congrArg Fin.val he; norm_num at this
  have hC : IsJordanCurve p.trace := by
    rw [← p.toPrePolygon_carrier hn hp]
    exact (p.toPrePolygon hn hp).isJordanCurve_carrier
  have hconn : IsPreconnected ((p.trace ∪ Q.carrier) ∪
      ⋃ j, segment ℝ (Q.vertex j) (foot (Q.vertex j))) := by
    rw [union_comm p.trace Q.carrier]
    exact isPreconnected_union_bridges Q.isJordanCurve_carrier.isConnected
      hC.isConnected.isPreconnected (fun _ ↦ Q.vertex_mem_carrier) hfoot
  refine ⟨points, hd, ⟨hthree, ?_, ?_⟩, hpoint, hverts, hQverts⟩
  · apply Graph.connected_of_isPreconnected_pointSet hd
    · rwa [hpoint]
    · exact ⟨p.vertex 0, hverts 0⟩
  · intro z _
    apply connected_deleteVerts_of_punctured hd z
    · rw [hpoint, union_comm p.trace Q.carrier]
      exact isPreconnected_punctured_two_curves_bridges Q.isJordanCurve_carrier hC
        (fun _ ↦ Q.vertex_mem_carrier) hfoot hdis z
    · obtain ⟨w, hw, hwz, _⟩ := hthree.exists_ne_ne z z
      exact ⟨w, hw, hwz⟩

end Reeken.Geometry.InscribedPolygon
