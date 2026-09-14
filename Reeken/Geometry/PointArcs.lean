import Reeken.Geometry.PolygonArcs

/-! # Cutting a polygon at points on its edges

For different edges, the cuts follow cyclic edge order. On a single edge, the
forward cut is the segment between the points. Its interpretation as the forward
arc uses their order along that edge; the estimates below do not need that order.
-/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} (p : InscribedPolygon f)

def edge (i : Fin (p.n + 1)) : Set E :=
  segment ℝ (p.vertex i) (p.vertex (nextIndex p.n i))

def forwardPointArc (a b : Fin (p.n + 1)) (x y : E) : Set E :=
  if a = b then segment ℝ x y else
    segment ℝ x (p.vertex (nextIndex p.n a)) ∪
      {z | ∃ i, a < i ∧ i < b ∧ z ∈ p.edge i} ∪ segment ℝ (p.vertex b) y

def backwardPointArc (a b : Fin (p.n + 1)) (x y : E) : Set E :=
  segment ℝ y (p.vertex (nextIndex p.n b)) ∪
    {z | ∃ i, (i < a ∨ b < i) ∧ z ∈ p.edge i} ∪ segment ℝ (p.vertex a) x

theorem forwardPointArc_subset {a b : Fin (p.n + 1)} (hab : a < b)
    {x y : E} (hx : x ∈ p.edge a) (hy : y ∈ p.edge b) :
    p.forwardPointArc a b x y ⊆ p.forwardArc a b ∪ p.edge b := by
  rw [forwardPointArc, if_neg hab.ne]
  rintro z ((hz | ⟨i, hai, hib, hz⟩) | hz)
  · exact Or.inl (Or.inr ⟨a, le_rfl, hab,
      (convex_segment _ _).segment_subset hx (right_mem_segment ℝ _ _) hz⟩)
  · exact Or.inl (Or.inr ⟨i, hai.le, hib, hz⟩)
  · exact Or.inr ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hy hz)

theorem backwardPointArc_subset {a b : Fin (p.n + 1)}
    {x y : E} (hx : x ∈ p.edge a) (hy : y ∈ p.edge b) :
    p.backwardPointArc a b x y ⊆ p.backwardArc a b ∪ p.edge a := by
  rintro z ((hz | ⟨i, hi, hz⟩) | hz)
  · exact Or.inl (Or.inr ⟨b, Or.inr le_rfl,
      (convex_segment _ _).segment_subset hy (right_mem_segment ℝ _ _) hz⟩)
  · exact Or.inl (Or.inr ⟨i, hi.imp id le_of_lt, hz⟩)
  · exact Or.inr ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hx hz)

/-- Filling just the two cut edges covers the original polygon. This weaker form
of the arc-cover identity suffices to rule out both arcs lying in one monad. -/
theorem trace_subset_pointArcs_edges {a b : Fin (p.n + 1)} (x y : E) :
    p.trace ⊆ ((p.forwardPointArc a b x y ∪ p.backwardPointArc a b x y) ∪
      p.edge a) ∪ p.edge b := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  by_cases hia : i = a
  · exact Or.inl (Or.inr (hia ▸ hi))
  by_cases hib : i = b
  · exact Or.inr (hib ▸ hi)
  by_cases hai : a < i
  · by_cases hib' : i < b
    · have hab' : a ≠ b := (hai.trans hib').ne
      exact Or.inl (Or.inl (Or.inl (by
        rw [forwardPointArc, if_neg hab']
        exact Or.inl (Or.inr ⟨i, hai, hib', hi⟩))))
    · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr
        ⟨i, Or.inr (lt_of_le_of_ne (le_of_not_gt hib') (fun h ↦ hib h.symm)), hi⟩))))
  · have hia' : i < a := lt_of_le_of_ne (le_of_not_gt hai) hia
    exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i, Or.inl hia', hi⟩))))

end Reeken.Geometry.InscribedPolygon
