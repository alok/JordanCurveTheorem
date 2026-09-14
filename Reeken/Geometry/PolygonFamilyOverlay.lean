import Reeken.Geometry.SquareTwoConnected

/-! # Overlaying a finite family of polygons attached at two points each

Each added polygon meets the base simple curve at two distinct points, so their
union remains connected after deleting any point. Subdivision gives a finite
2-connected drawing of the entire arrangement, including all base vertices.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

noncomputable def polygonFamilyPieces {k : ℕ} (q : Fin (k + 1) → Σ m, ClosedPolygon m) : List Piece :=
  (List.ofFn fun j ↦ (q j).2.pieces).flatten

theorem cover_polygonFamilyPieces {k : ℕ} (q : Fin (k + 1) → Σ m, ClosedPolygon m) :
    cover (polygonFamilyPieces q) = ⋃ j, (q j).2.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
    obtain ⟨L, hL, hPL⟩ := List.mem_flatten.mp hP
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [← ClosedPolygon.cover_pieces]
    exact mem_iUnion₂.mpr ⟨P, hPL, hxP⟩
  · intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    rw [← ClosedPolygon.cover_pieces] at hxj
    obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hxj
    exact mem_iUnion₂.mpr ⟨P, List.mem_flatten.mpr
      ⟨(q j).2.pieces, List.mem_ofFn.mpr ⟨j, rfl⟩, hP⟩, hxP⟩

theorem polygonFamilyPieces_nondeg {k : ℕ} (q : Fin (k + 1) → Σ m, ClosedPolygon m) :
    ∀ P ∈ polygonFamilyPieces q, P.Nondeg := by
  intro P hP
  obtain ⟨L, hL, hPL⟩ := List.mem_flatten.mp hP
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
  exact (q j).2.pieces_nondeg P hPL

theorem isPreconnected_punctured_family {ι : Type*} [Nonempty ι]
    {C : Set Plane} {Q : ι → Set Plane} (hC : IsJordanCurve C)
    (hQ : ∀ j, IsJordanCurve (Q j))
    (hmeet : ∀ j, ∃ x ∈ C ∩ Q j, ∃ y ∈ C ∩ Q j, x ≠ y) (z : Plane) :
    IsPreconnected ((C ∪ ⋃ j, Q j) \ {z}) := by
  have hpiece : ∀ j, IsPreconnected ((C ∪ Q j) \ {z}) := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := hmeet j
    exact isPreconnected_punctured_union (isPreconnected_punctured_jordan hC)
      (isPreconnected_punctured_jordan (hQ j)) hx hy hxy z
  obtain ⟨w, hwC, hwz⟩ := (isPathConnected_punctured_jordan hC z).nonempty
  have hcommon : (⋂ j, (C ∪ Q j) \ {z}).Nonempty :=
    ⟨w, mem_iInter.mpr fun _ ↦ ⟨Or.inl hwC, hwz⟩⟩
  have h := isPreconnected_iUnion hcommon hpiece
  simpa only [← iUnion_sdiff, ← union_iUnion] using h

namespace InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

/-- A finite drawing for the actual base polygon and a whole attached polygon family. -/
theorem Simple.exists_family_overlay (hp : p.Simple) (hn : 2 ≤ p.n)
    {k : ℕ} (q : Fin (k + 1) → Σ m, ClosedPolygon m)
    (hmeet : ∀ j, ∃ x ∈ p.trace ∩ (q j).2.carrier,
      ∃ y ∈ p.trace ∩ (q j).2.carrier, x ≠ y) :
    ∃ points : List Plane,
      Graph.IsDrawing (overlayGraph (p.pieces ++ polygonFamilyPieces q) points) segmentDrawing ∧
      (overlayGraph (p.pieces ++ polygonFamilyPieces q) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (p.pieces ++ polygonFamilyPieces q) points) segmentDrawing =
        p.trace ∪ ⋃ j, (q j).2.carrier ∧
      ∀ i, p.vertex i ∈ V(overlayGraph (p.pieces ++ polygonFamilyPieces q) points) := by
  let pieces := p.pieces ++ polygonFamilyPieces q
  have hnd : ∀ P ∈ pieces, P.Nondeg := by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact p.pieces_nondeg (by omega) P hP
    · exact polygonFamilyPieces_nondeg q P hP
  obtain ⟨points, hmarked, hEnds, hMeets⟩ := exists_marked_cut_points pieces (List.ofFn p.vertex)
  have hd := overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have hcover : cover pieces = p.trace ∪ ⋃ j, (q j).2.carrier := by
    change cover (p.pieces ++ polygonFamilyPieces q) = _
    rw [cover_append, p.cover_pieces, cover_polygonFamilyPieces]
  have hpoint : Graph.pointSet (overlayGraph pieces points) segmentDrawing =
      p.trace ∪ ⋃ j, (q j).2.carrier := by rw [overlayGraph_pointSet, hcover]
  have hverts : ∀ i, p.vertex i ∈ V(overlayGraph pieces points) := by
    intro i
    apply mem_overlay_vertex_of_cut hnd (hmarked (List.mem_ofFn.mpr ⟨i, rfl⟩))
    rw [hcover]
    exact Or.inl (p.vertex_mem_trace i)
  have hthree : (overlayGraph pieces points).HasThreeVertices := by
    refine ⟨p.vertex ⟨0, by omega⟩, hverts _, p.vertex ⟨1, by omega⟩, hverts _,
      p.vertex ⟨2, by omega⟩, hverts _, ?_, ?_, ?_⟩
    all_goals
      apply p.vertex_injective.ne
      exact fun he ↦ by have := congrArg Fin.val he; norm_num at this
  have hC : IsJordanCurve p.trace := by
    rw [← p.toPrePolygon_carrier hn hp]
    exact (p.toPrePolygon hn hp).isJordanCurve_carrier
  have hconn : IsPreconnected (p.trace ∪ ⋃ j, (q j).2.carrier) := by
    have hcommon : (⋂ j, p.trace ∪ (q j).2.carrier).Nonempty :=
      ⟨p.vertex 0, mem_iInter.mpr fun _ ↦ Or.inl (p.vertex_mem_trace 0)⟩
    have hpieces : ∀ j, IsPreconnected (p.trace ∪ (q j).2.carrier) := by
      intro j
      obtain ⟨x, hx, _⟩ := hmeet j
      exact hC.isConnected.isPreconnected.union x hx.1 hx.2
        (q j).2.isJordanCurve_carrier.isConnected.isPreconnected
    simpa only [← union_iUnion] using isPreconnected_iUnion hcommon hpieces
  refine ⟨points, hd, ⟨hthree, ?_, ?_⟩, hpoint, hverts⟩
  · apply Graph.connected_of_isPreconnected_pointSet hd
    · rwa [hpoint]
    · exact ⟨p.vertex 0, hverts 0⟩
  · intro z _
    apply connected_deleteVerts_of_punctured hd z
    · rw [hpoint]
      exact isPreconnected_punctured_family hC (fun j ↦ (q j).2.isJordanCurve_carrier) hmeet z
    · obtain ⟨w, hw, hwz, _⟩ := hthree.exists_ne_ne z z
      exact ⟨w, hw, hwz⟩

end InscribedPolygon
end Reeken.Geometry
