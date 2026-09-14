import Reeken.Geometry.PolygonTopology

/-! # Compact polygon arcs and their nearby parameters -/

open Set Metric

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}
variable (p : InscribedPolygon f) (a b : Fin (p.n + 1))

omit [NormedSpace ℝ E] in
theorem maxEdge_nonneg : 0 ≤ p.maxEdge := dist_nonneg.trans (p.edgeLength_le_maxEdge 0)

theorem isCompact_forwardArc : IsCompact (p.forwardArc a b) := by
  have he : p.forwardArc a b = {p.vertex a} ∪
      ⋃ j : Fin (p.n + 1), ⋃ (_ : a ≤ j ∧ j < b), p.edge j := by
    ext x
    simp [forwardArc, edge, and_assoc]
  rw [he]
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro j
  apply isCompact_iUnion
  intro _
  rw [edge, segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem isCompact_backwardArc : IsCompact (p.backwardArc a b) := by
  have he : p.backwardArc a b = {p.vertex b} ∪
      ⋃ j : Fin (p.n + 1), ⋃ (_ : j < a ∨ b ≤ j), p.edge j := by
    ext x
    simp [backwardArc, edge]
  rw [he]
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro j
  apply isCompact_iUnion
  intro _
  rw [edge, segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem forwardArc_nonempty : (p.forwardArc a b).Nonempty := ⟨p.vertex a, Or.inl rfl⟩

theorem backwardArc_nonempty : (p.backwardArc a b).Nonempty := ⟨p.vertex b, Or.inl rfl⟩

theorem exists_forwardArc_parameter (hab : a ≤ b) {x : E} (hx : x ∈ p.forwardArc a b) :
    ∃ t ∈ Icc 0 1, t ∈ Icc (p.time a) (p.time b) ∧ dist x (f t) ≤ p.maxEdge := by
  rcases hx with rfl | ⟨j, haj, hjb, hx⟩
  · exact ⟨p.time a, Ico_subset_Icc_self (p.time_mem a),
      ⟨le_rfl, p.increasing.monotone hab⟩, by simpa [vertex] using p.maxEdge_nonneg⟩
  · refine ⟨p.time j, Ico_subset_Icc_self (p.time_mem j),
      ⟨p.increasing.monotone haj, (p.increasing hjb).le⟩, ?_⟩
    rw [dist_comm]
    exact (dist_left_le_of_mem_segment hx).trans (p.edgeLength_le_maxEdge j)

theorem exists_backwardArc_parameter {x : E} (hx : x ∈ p.backwardArc a b) :
    ∃ t ∈ Icc 0 1, (t ≤ p.time a ∨ p.time b ≤ t) ∧ dist x (f t) ≤ p.maxEdge := by
  rcases hx with rfl | ⟨j, hj, hx⟩
  · exact ⟨p.time b, Ico_subset_Icc_self (p.time_mem b), Or.inr le_rfl,
      by simpa [vertex] using p.maxEdge_nonneg⟩
  · refine ⟨p.time j, Ico_subset_Icc_self (p.time_mem j),
      hj.imp (fun h ↦ (p.increasing h).le) (fun h ↦ p.increasing.monotone h), ?_⟩
    rw [dist_comm]
    exact (dist_left_le_of_mem_segment hx).trans (p.edgeLength_le_maxEdge j)

end Reeken.Geometry.InscribedPolygon
