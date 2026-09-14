import Reeken.Geometry.EdgeRectangles
import Reeken.Geometry.PolygonTopology
import Reeken.Geometry.SimplePolygon

/-! # The finite family of narrow rectangles covering an inscribed polygon -/

open Set Metric Schoenflies

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

noncomputable def edgeDirection (j : Fin (p.n + 1)) : Plane :=
  Plane.dir (p.vertex (nextIndex p.n j) - p.vertex j)

theorem edgeDirection_isDirection (hn : 0 < p.n) (j : Fin (p.n + 1)) :
    Plane.IsDirection (p.edgeDirection j) := by
  apply Plane.isDirection_dir
  intro h
  exact nextIndex_ne_self hn j (p.vertex_injective (sub_eq_zero.mp h))

theorem edgeLength_smul_edgeDirection (hn : 0 < p.n) (j : Fin (p.n + 1)) :
    p.edgeLength j • p.edgeDirection j = p.vertex (nextIndex p.n j) - p.vertex j := by
  have hne : p.vertex (nextIndex p.n j) - p.vertex j ≠ 0 := by
    intro h
    exact nextIndex_ne_self hn j (p.vertex_injective (sub_eq_zero.mp h))
  rw [edgeDirection, Plane.dir, edgeLength, dist_eq_norm']
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]

noncomputable def closedRectangle (ε : ℝ) (j : Fin (p.n + 1)) : Set Plane :=
  closedEdgeRectangle (p.vertex j) (p.edgeDirection j) (p.edgeLength j) ε

noncomputable def openRectangle (ε : ℝ) (j : Fin (p.n + 1)) : Set Plane :=
  openEdgeRectangle (p.vertex j) (p.edgeDirection j) (p.edgeLength j) ε

noncomputable def rectangleCover (ε : ℝ) : Set Plane := ⋃ j, p.closedRectangle ε j

noncomputable def openRectangleCover (ε : ℝ) : Set Plane := ⋃ j, p.openRectangle ε j

theorem isCompact_rectangleCover (hn : 0 < p.n) (ε : ℝ) :
    IsCompact (p.rectangleCover ε) :=
  isCompact_iUnion fun j ↦ isCompact_closedEdgeRectangle _ (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) ε

theorem isOpen_openRectangleCover (ε : ℝ) : IsOpen (p.openRectangleCover ε) :=
  isOpen_iUnion fun _ ↦ isOpen_openEdgeRectangle _ _ _ _

theorem openRectangleCover_subset (ε : ℝ) : p.openRectangleCover ε ⊆ p.rectangleCover ε :=
  iUnion_mono fun _ ↦ openEdgeRectangle_subset_closed _ _ _ _

theorem mem_openRectangleCover_of_near_trace (hn : 0 < p.n) {ε : ℝ} (hε : 0 < ε)
    {x y : Plane} (hy : y ∈ p.trace) (hxy : dist x y ≤ ε) : x ∈ p.openRectangleCover ε := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  apply mem_iUnion.mpr
  refine ⟨j, mem_openEdgeRectangle_of_near_edge (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) hε ?_ hxy⟩
  rwa [p.edgeLength_smul_edgeDirection hn, add_sub_cancel]

theorem rectangleCover_near_trace (hn : 0 < p.n) {ε : ℝ} {x : Plane}
    (hx : x ∈ p.rectangleCover ε) :
    ∃ y ∈ p.trace, dist x y ≤ p.maxEdge + 4 * ε := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  refine ⟨p.vertex j, p.vertex_mem_trace j, ?_⟩
  exact (dist_initial_le_of_mem_closedEdgeRectangle (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) hj).trans
    (by linarith [p.edgeLength_le_maxEdge j])

theorem vertex_mem_openRectangle (hn : 0 < p.n) {ε : ℝ} (hε : 0 < ε) (j : Fin (p.n + 1)) :
    p.vertex j ∈ p.openRectangle ε j := by
  apply mem_openEdgeRectangle_of_near_edge (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) hε (left_mem_segment ℝ _ _)
  simpa using hε.le

theorem openRectangle_subset_interior (ε : ℝ) (j : Fin (p.n + 1)) :
    p.openRectangle ε j ⊆ interior (p.closedRectangle ε j) :=
  (isOpen_openEdgeRectangle _ _ _ _).subset_interior_iff.mpr
    (openEdgeRectangle_subset_closed _ _ _ _)

/-- Two sufficiently separated vertices prevent any narrow edge rectangle from
containing the entire polygon. -/
theorem exists_vertex_outside_rectangle (hn : 0 < p.n) {ε : ℝ}
    {a b : Fin (p.n + 1)} (hfar : 2 * (p.maxEdge + 4 * ε) < dist (p.vertex a) (p.vertex b))
    (j : Fin (p.n + 1)) : ∃ k, p.vertex k ∉ p.closedRectangle ε j := by
  by_contra h
  push Not at h
  have ha := dist_initial_le_of_mem_closedEdgeRectangle (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) (h a)
  have hb := dist_initial_le_of_mem_closedEdgeRectangle (p.edgeDirection_isDirection hn j)
    (show 0 ≤ p.edgeLength j from dist_nonneg) (h b)
  have ht := dist_triangle (p.vertex a) (p.vertex j) (p.vertex b)
  rw [dist_comm (p.vertex j) (p.vertex b)] at ht
  linarith [p.edgeLength_le_maxEdge j]

/-- Include every possible shortest connection, so finite selected arrangements inherit
the same uniform bound without inspecting their chosen vertices or intersections. -/
def nearestConnectorCover (ε : ℝ) : Set Plane :=
  {z | ∃ x ∈ p.rectangleCover ε, ∃ y, IsNearest p.trace x y ∧ z ∈ segment ℝ x y}

theorem nearestConnectorCover_near_trace (hn : 0 < p.n) {ε : ℝ} {z : Plane}
    (hz : z ∈ p.nearestConnectorCover ε) :
    ∃ y ∈ p.trace, dist z y ≤ p.maxEdge + 4 * ε := by
  obtain ⟨x, hx, y, hy, hz⟩ := hz
  obtain ⟨a, ha, hxa⟩ := p.rectangleCover_near_trace hn hx
  refine ⟨y, hy.1, ?_⟩
  have hzy : dist z y ≤ dist x y := by
    have h := dist_add_dist_of_mem_segment hz
    linarith [dist_nonneg (x := x) (y := z)]
  exact hzy.trans ((hy.2 a ha).trans hxa)

end Reeken.Geometry.InscribedPolygon
