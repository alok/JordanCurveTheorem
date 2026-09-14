import Reeken.Geometry.SpokeConnectivity
import Reeken.Geometry.MarkedOverlay
import Reeken.Geometry.DrawingDeletion
import Schoenflies.Graph.Trace

/-! # Finite plane drawings with a family of doubly attached straight segments

Degenerate connections are omitted from the edge list: their single point already
lies in the old drawing. All old and new intersections are subdivided. The actual
resulting drawing remains 2-connected by punctured connectivity of its carrier.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

noncomputable def attachedPieces {ι : Type*} [Fintype ι]
    (pieces : List Piece) (a b : ι → Plane) : List Piece := by
  classical
  exact pieces ++ ((Finset.univ.toList.map fun i ↦ (a i, b i)).filter fun (P : Piece) ↦ P.Nondeg)

theorem attachedPieces_nondeg {ι : Type*} [Fintype ι]
    {pieces : List Piece} (hpieces : ∀ P ∈ pieces, P.Nondeg) (a b : ι → Plane) :
    ∀ P ∈ attachedPieces pieces a b, P.Nondeg := by
  classical
  intro P hP
  rcases List.mem_append.mp hP with hP | hP
  · exact hpieces P hP
  · exact of_decide_eq_true (List.mem_filter.mp hP).2

theorem cover_attachedPieces {ι : Type*} [Fintype ι]
    (pieces : List Piece) (a b : ι → Plane) (ha : ∀ i, a i ∈ cover pieces) :
    cover (attachedPieces pieces a b) = cover pieces ∪ ⋃ i, segment ℝ (a i) (b i) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
    rcases List.mem_append.mp hP with hP | hP
    · exact Or.inl (mem_iUnion₂.mpr ⟨P, hP, hxP⟩)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hP).1
      exact Or.inr (mem_iUnion.mpr ⟨i, hxP⟩)
  · rintro (hx | hx)
    · obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨P, List.mem_append_left _ hP, hxP⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      by_cases hi : a i = b i
      · have hxai : x = a i := by simpa only [← hi, segment_same, mem_singleton_iff] using hxi
        obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp (hxai ▸ ha i)
        exact mem_iUnion₂.mpr ⟨P, List.mem_append_left _ hP, hxP⟩
      · refine mem_iUnion₂.mpr ⟨(a i, b i), List.mem_append_right _ ?_, hxi⟩
        apply List.mem_filter.mpr
        exact ⟨List.mem_map.mpr ⟨i, by simp, rfl⟩, decide_eq_true hi⟩

/-- Add the given straight connections and retain all requested old vertices. -/
theorem exists_attached_segments_overlay {ι : Type*} [Fintype ι] [Nonempty ι]
    (pieces : List Piece) (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hpunctured : ∀ z, IsPreconnected (cover pieces \ {z}))
    (a b : ι → Plane) (ha : ∀ i, a i ∈ cover pieces) (hb : ∀ i, b i ∈ cover pieces)
    {x y w : Plane} (hx : x ∈ cover pieces) (hy : y ∈ cover pieces) (hw : w ∈ cover pieces)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) (marked : List Plane) :
    ∃ points : List Plane, marked ⊆ points ∧
      Graph.IsDrawing (overlayGraph (attachedPieces pieces a b) points) segmentDrawing ∧
      (overlayGraph (attachedPieces pieces a b) points).IsTwoConnected ∧
      Graph.pointSet (overlayGraph (attachedPieces pieces a b) points) segmentDrawing =
        cover pieces ∪ ⋃ i, segment ℝ (a i) (b i) ∧
      ∀ z ∈ marked, z ∈ cover pieces → z ∈ V(overlayGraph (attachedPieces pieces a b) points) := by
  let full := attachedPieces pieces a b
  have hfullnd := attachedPieces_nondeg hnd a b
  obtain ⟨points, hmarked, hEnds, hMeets⟩ := exists_marked_cut_points full (marked ++ [x, y, w])
  have hd := overlayGraph_isDrawing full points hfullnd hEnds hMeets
  have hcover : cover full = cover pieces ∪ ⋃ i, segment ℝ (a i) (b i) :=
    cover_attachedPieces pieces a b ha
  have hpoint : Graph.pointSet (overlayGraph full points) segmentDrawing =
      cover pieces ∪ ⋃ i, segment ℝ (a i) (b i) := by rw [overlayGraph_pointSet, hcover]
  have hverts : ∀ z ∈ marked ++ [x, y, w], z ∈ cover pieces →
      z ∈ V(overlayGraph full points) := by
    intro z hz hzC
    apply mem_overlay_vertex_of_cut hfullnd (hmarked hz)
    rw [hcover]
    exact Or.inl hzC
  have hthree : (overlayGraph full points).HasThreeVertices :=
    ⟨x, hverts x (by simp) hx, y, hverts y (by simp) hy, w, hverts w (by simp) hw, hxy, hxw, hyw⟩
  have hnewconn : IsPreconnected (cover pieces ∪ ⋃ i, segment ℝ (a i) (b i)) := by
    have hcommon : (⋂ i, cover pieces ∪ segment ℝ (a i) (b i)).Nonempty :=
      ⟨x, mem_iInter.mpr fun _ ↦ Or.inl hx⟩
    have hpieces : ∀ i, IsPreconnected (cover pieces ∪ segment ℝ (a i) (b i)) :=
      fun i ↦ hconn.union (a i) (ha i) (left_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected
    simpa only [← union_iUnion] using isPreconnected_iUnion hcommon hpieces
  refine ⟨points, fun z hz ↦ hmarked (List.mem_append_left _ hz), hd, ⟨hthree, ?_, ?_⟩,
    hpoint, fun z hz hzC ↦ hverts z (List.mem_append_left _ hz) hzC⟩
  · apply Graph.connected_of_isPreconnected_pointSet hd
    · rwa [hpoint]
    · exact ⟨x, hverts x (by simp) hx⟩
  · intro z _
    apply connected_deleteVerts_of_punctured hd z
    · rw [hpoint]
      have hne : (cover pieces \ {z}).Nonempty := by
        by_cases hxz : x = z
        · exact ⟨y, hy, fun hyz ↦ hxy (hxz.trans hyz.symm)⟩
        · exact ⟨x, hx, hxz⟩
      exact isPreconnected_punctured_union_segments (hpunctured z) hne ha hb
    · obtain ⟨v, hv, hvz, _⟩ := hthree.exists_ne_ne z z
      exact ⟨v, hv, hvz⟩

end Reeken.Geometry
