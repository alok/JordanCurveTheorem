import Reeken.Geometry.PointArcs
import Reeken.Geometry.NearestSegments
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-! # Compactness, paths, and nearest points for polygon boundaries -/

open Set Metric

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

theorem vertex_mem_trace (p : InscribedPolygon f) (i : Fin (p.n + 1)) : p.vertex i ∈ p.trace :=
  mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

theorem edge_subset_trace (p : InscribedPolygon f) (i : Fin (p.n + 1)) : p.edge i ⊆ p.trace :=
  subset_iUnion (fun j ↦ p.edge j) i

theorem isCompact_trace (p : InscribedPolygon f) : IsCompact p.trace := by
  apply isCompact_iUnion
  intro i
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem trace_nonempty (p : InscribedPolygon f) : p.trace.Nonempty :=
  ⟨p.vertex 0, p.vertex_mem_trace 0⟩

theorem joinedIn_vertex (p : InscribedPolygon f) (i : Fin (p.n + 1)) :
    JoinedIn p.trace (p.vertex 0) (p.vertex i) := by
  induction i using Fin.induction with
  | zero => exact JoinedIn.refl (p.vertex_mem_trace 0)
  | succ i ih =>
    apply ih.trans
    have hc := (convex_segment (p.vertex i.castSucc) (p.vertex i.succ)).isPathConnected
      ⟨_, left_mem_segment ℝ _ _⟩
    apply (hc.joinedIn _ (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _)).mono
    simpa only [edge, nextIndex_castSucc] using p.edge_subset_trace i.castSucc

theorem isPathConnected_trace (p : InscribedPolygon f) : IsPathConnected p.trace := by
  refine ⟨p.vertex 0, p.vertex_mem_trace 0, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  apply (p.joinedIn_vertex i).trans
  have hc := (convex_segment (p.vertex i) (p.vertex (nextIndex p.n i))).isPathConnected
    ⟨_, left_mem_segment ℝ _ _⟩
  exact (hc.joinedIn _ (left_mem_segment ℝ _ _) _ hi).mono (p.edge_subset_trace i)

theorem trace_subset_closedBall (p : InscribedPolygon f) {a : E} {r : ℝ}
    (h : ∀ i, p.vertex i ∈ closedBall a r) : p.trace ⊆ closedBall a r := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact (convex_closedBall a r).segment_subset (h i) (h _) hi

/-- One standard ball contains every inscribed polygon of the fixed loop. -/
theorem exists_uniform_trace_bound (f : SimpleLoop E) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : InscribedPolygon f, p.trace ⊆ closedBall 0 r := by
  have hc : IsCompact (f '' Icc 0 1) := isCompact_Icc.image_of_continuousOn f.continuousOn
  obtain ⟨r, hr, hsub⟩ := hc.isBounded.subset_closedBall_lt 0 0
  refine ⟨r, hr, fun p ↦ p.trace_subset_closedBall ?_⟩
  intro i
  exact hsub ⟨p.time i, Ico_subset_Icc_self (p.time_mem i), rfl⟩

theorem exists_nearest_on_trace (p : InscribedPolygon f) (a : E) :
    ∃ b, IsNearest p.trace a b :=
  exists_nearest_of_isCompact p.isCompact_trace p.trace_nonempty a

end Reeken.Geometry.InscribedPolygon
