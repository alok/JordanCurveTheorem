import Reeken.Geometry.ArcTopology

/-! # Paths along the two polygon arcs

The forward path follows consecutive edges. The backward path follows the remaining
edges through the closing edge. These facts do not require polygon simplicity.
-/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} (p : InscribedPolygon f)

theorem joinedIn_forwardArc {a b j : Fin (p.n + 1)} (haj : a ≤ j) (hjb : j ≤ b) :
    JoinedIn (p.forwardArc a b) (p.vertex a) (p.vertex j) := by
  induction j using Fin.induction with
  | zero =>
    have ha : a = 0 := le_antisymm haj (Fin.zero_le a)
    subst a
    exact JoinedIn.refl (Or.inl rfl)
  | succ j ih =>
    by_cases ha : a = j.succ
    · subst a
      exact JoinedIn.refl (Or.inl rfl)
    have haj' : a ≤ j.castSucc := by
      have := lt_of_le_of_ne haj ha
      exact Nat.le_of_lt_succ this
    apply (ih haj' ((Fin.castSucc_le_succ j).trans hjb)).trans
    have hc := (convex_segment (p.vertex j.castSucc) (p.vertex j.succ)).isPathConnected
      ⟨_, left_mem_segment ℝ _ _⟩
    apply (hc.joinedIn _ (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _)).mono
    intro x hx
    exact Or.inr ⟨j.castSucc, haj', Fin.castSucc_lt_succ.trans_le hjb,
      by simpa only [nextIndex_castSucc] using hx⟩

theorem isPathConnected_forwardArc (a b : Fin (p.n + 1)) :
    IsPathConnected (p.forwardArc a b) := by
  refine ⟨p.vertex a, Or.inl rfl, ?_⟩
  rintro x (rfl | ⟨j, haj, hjb, hx⟩)
  · exact JoinedIn.refl (Or.inl rfl)
  · apply (p.joinedIn_forwardArc haj hjb.le).trans
    have hc := (convex_segment (p.vertex j) (p.vertex (nextIndex p.n j))).isPathConnected
      ⟨_, left_mem_segment ℝ _ _⟩
    exact (hc.joinedIn _ (left_mem_segment ℝ _ _) _ hx).mono
      (fun _ hy ↦ Or.inr ⟨j, haj, hjb, hy⟩)

theorem forwardArc_tail_subset_backwardArc (a b : Fin (p.n + 1)) :
    p.forwardArc b (Fin.last p.n) ⊆ p.backwardArc a b := by
  rintro x (rfl | ⟨j, hbj, _, hx⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨j, Or.inr hbj, hx⟩

theorem closing_edge_subset_backwardArc (a b : Fin (p.n + 1)) :
    p.edge (Fin.last p.n) ⊆ p.backwardArc a b :=
  fun _ hx ↦ Or.inr ⟨Fin.last p.n, Or.inr (Fin.le_last b), hx⟩

theorem forwardArc_head_subset_backwardArc (a b : Fin (p.n + 1)) :
    p.forwardArc 0 a ⊆ p.backwardArc a b := by
  rintro x (rfl | ⟨j, _, hja, hx⟩)
  · apply p.closing_edge_subset_backwardArc a b
    simpa only [edge, nextIndex_last] using
      (right_mem_segment ℝ (p.vertex (Fin.last p.n)) (p.vertex 0))
  · exact Or.inr ⟨j, Or.inl hja, hx⟩

theorem joinedIn_backwardArc_zero (a b : Fin (p.n + 1)) :
    JoinedIn (p.backwardArc a b) (p.vertex b) (p.vertex 0) := by
  apply ((p.joinedIn_forwardArc (a := b) (Fin.le_last b) le_rfl).mono
    (p.forwardArc_tail_subset_backwardArc a b)).trans
  have hc := (convex_segment (p.vertex (Fin.last p.n)) (p.vertex 0)).isPathConnected
    ⟨_, left_mem_segment ℝ _ _⟩
  apply (hc.joinedIn _ (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _)).mono
  simpa only [edge, nextIndex_last] using p.closing_edge_subset_backwardArc a b

theorem joinedIn_backwardArc {a b j : Fin (p.n + 1)} (hj : j ≤ a ∨ b ≤ j) :
    JoinedIn (p.backwardArc a b) (p.vertex b) (p.vertex j) := by
  rcases hj with hja | hbj
  · exact (p.joinedIn_backwardArc_zero a b).trans
      ((p.joinedIn_forwardArc (Fin.zero_le j) hja).mono
        (p.forwardArc_head_subset_backwardArc a b))
  · exact (p.joinedIn_forwardArc hbj (Fin.le_last j)).mono
      (p.forwardArc_tail_subset_backwardArc a b)

theorem isPathConnected_backwardArc (a b : Fin (p.n + 1)) :
    IsPathConnected (p.backwardArc a b) := by
  refine ⟨p.vertex b, Or.inl rfl, ?_⟩
  rintro x (rfl | ⟨j, hj, hx⟩)
  · exact JoinedIn.refl (Or.inl rfl)
  · apply (p.joinedIn_backwardArc (hj.imp (fun h ↦ h.le) id)).trans
    have hc := (convex_segment (p.vertex j) (p.vertex (nextIndex p.n j))).isPathConnected
      ⟨_, left_mem_segment ℝ _ _⟩
    exact (hc.joinedIn _ (left_mem_segment ℝ _ _) _ hx).mono
      (fun _ hy ↦ Or.inr ⟨j, hj, hy⟩)

end Reeken.Geometry.InscribedPolygon
