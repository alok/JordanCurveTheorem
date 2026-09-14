import Reeken.Geometry.TriangleVisibility

/-! # Empty neighbor triangles

If the triangle formed by a polygon vertex and its two neighbors contains no
other polygon vertex, its interior contains no polygon edge. The visibility
argument supplies a forbidden crossing if an edge were to enter the triangle.
-/

open Set Schoenflies

namespace Reeken.Geometry

def cornerTriangle {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3)) : ClosedPolygon 0 :=
  Schoenflies.triangle (a := P.vertex i) (b := P.vertex (i + 1)) (c := P.vertex (i - 1))
    (by rw [Plane.det_comm]; exact neg_ne_zero.mpr (P.corner i))

theorem cornerTriangle_range {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    range (cornerTriangle P i).vertex = {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} :=
  triangle_range_vertices _

theorem empty_corner_triangle_disjoint_carrier {m : ℕ} (P : ClosedPolygon m)
    (i : ZMod (m + 3))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) :
    Disjoint (inside (cornerTriangle P i).carrier) P.carrier := by
  let T := cornerTriangle P i
  have he0 : T.edge 0 = P.edge i := rfl
  have he2 : T.edge 2 = P.edge (i - 1) := by
    change segment ℝ (P.vertex (i - 1)) (P.vertex i) =
      segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
    rw [sub_add_cancel]
  refine disjoint_left.mpr ?_
  intro z hzT hzP
  obtain ⟨j, hzj⟩ := mem_iUnion.mp hzP
  have hji : j ≠ i := by
    intro he
    have hzedge : z ∈ T.edge 0 := by rw [he0, ← he]; exact hzj
    exact hzT.1 (ClosedPolygon.edge_subset_carrier hzedge)
  have hjprev : j ≠ i - 1 := by
    intro he
    have hzedge : z ∈ T.edge 2 := by rw [he2, ← he]; exact hzj
    exact hzT.1 (ClosedPolygon.edge_subset_carrier hzedge)
  have hnexti : j + 1 ≠ i := fun he ↦ hjprev (by linear_combination he)
  have hp : P.vertex j ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} →
      P.vertex j ∈ segment ℝ (P.vertex (i + 1)) (P.vertex (i - 1)) := by
    intro hj
    rw [← cornerTriangle_range P i] at hj
    rcases hempty j hj with he | rfl | rfl
    · exact False.elim (hji he)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hq : P.vertex (j + 1) ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} →
      P.vertex (j + 1) ∈ segment ℝ (P.vertex (i + 1)) (P.vertex (i - 1)) := by
    intro hj
    rw [← cornerTriangle_range P i] at hj
    rcases hempty (j + 1) hj with he | he | he
    · exact False.elim (hnexti he)
    · rw [he]; exact left_mem_segment ℝ _ _
    · rw [he]; exact right_mem_segment ℝ _ _
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  obtain ⟨x, hxj, hxsides, hxp, hxq⟩ := segment_crosses_triangle_side hdet hp hq hzT hzj
  have hmeet : x ∈ ({P.vertex j, P.vertex (j + 1)} : Set Plane) := by
    rcases hxsides with hx | hx
    · exact P.edges_meet j i hji ⟨hxj, hx⟩
    · apply P.edges_meet j (i - 1) hjprev ⟨hxj, ?_⟩
      rwa [sub_add_cancel]
  exact hmeet.elim hxp hxq

/-- At a strictly supported corner an empty neighbor triangle lies on the inside
of the polygon. Its closed interior therefore lies in the polygon's closed inside. -/
theorem empty_corner_triangle_inside {m : ℕ} (P : ClosedPolygon m)
    (i : ZMod (m + 3)) (F : Plane →L[ℝ] ℝ)
    (hF : ∀ x ∈ P.carrier, F x ≤ F (P.vertex i))
    (hprev : F (P.vertex (i - 1)) < F (P.vertex i))
    (hnext : F (P.vertex (i + 1)) < F (P.vertex i))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) :
    inside (cornerTriangle P i).carrier ⊆ inside P.carrier ∧
      closure (inside (cornerTriangle P i).carrier) ⊆ closure (inside P.carrier) := by
  let T := cornerTriangle P i
  have hTF : ∀ x ∈ T.carrier, F x ≤ F (P.vertex i) := by
    have hH : convexHull ℝ (range T.vertex) ⊆ {x | F x ≤ F (P.vertex i)} := by
      rw [cornerTriangle_range P i]
      apply convexHull_min
      · simp only [insert_subset_iff, singleton_subset_iff]
        change F (P.vertex i) ≤ F (P.vertex i) ∧
          F (P.vertex (i + 1)) ≤ F (P.vertex i) ∧ F (P.vertex (i - 1)) ≤ F (P.vertex i)
        exact ⟨le_rfl, hnext.le, hprev.le⟩
      · exact convex_halfSpace_le (show IsLinearMap ℝ F from ⟨F.map_add, F.map_smul⟩) (F (P.vertex i))
    exact (triangle_carrier_subset_hull T).trans hH
  obtain ⟨δP, hδP, hinP⟩ := exists_inward_bisector P i F hF hprev hnext
  obtain ⟨δT, hδT, hinT⟩ := exists_inward_bisector T 0 F hTF hprev hnext
  let ε := min δP δT / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεP : ε < δP := by dsimp [ε]; linarith [min_le_left δP δT]
  have hεT : ε < δT := by dsimp [ε]; linarith [min_le_right δP δT]
  have hbothP := hinP ε hε hεP
  have hbothT := hinT ε hε hεT
  have hsub : inside T.carrier ⊆ inside P.carrier := by
    apply T.isSeparating_carrier.isConnected_inside.isPreconnected.subset_left_of_subset_union
      P.isSeparating_carrier.isOpen_inside P.isSeparating_carrier.isOpen_outside disjoint_inside_outside
    · rw [inside_union_outside]
      exact (empty_corner_triangle_disjoint_carrier P i hempty).subset_compl_right
    · exact ⟨_, hbothT, hbothP⟩
  exact ⟨hsub, closure_mono hsub⟩

end Reeken.Geometry
