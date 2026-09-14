import Reeken.Geometry.PolygonEar
import Reeken.Geometry.TriangleBase

/-! # The diagonal of an empty neighbor triangle

For a polygon with more than three vertices, the base of an empty neighbor
triangle misses every polygon edge except at its ends. At a strictly supported
corner this open diagonal lies in the polygon's inside.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem vertex_notMem_empty_corner_base {m : ℕ} (P : ClosedPolygon m)
    (i : ZMod (m + 3))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) (j : ZMod (m + 3)) :
    P.vertex j ∉ openSegment ℝ (P.vertex (i + 1)) (P.vertex (i - 1)) := by
  intro hj
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  have hH : P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) := by
    rw [cornerTriangle_range]
    exact segment_subset_convexHull (by simp) (by simp)
      (openSegment_subset_segment ℝ _ _ hj)
  obtain ⟨hj0, hj1, hj2⟩ := triangleWeights_on_base hdet hj
  rcases hempty j hH with heq | heq | heq
  · rw [heq] at hj0
    have he := triangleWeights_vertices hdet 0 0
    change triangleWeights _ _ _ (P.vertex i) 0 = 1 at he
    linarith
  · rw [heq] at hj2
    have he := triangleWeights_vertices hdet 1 2
    norm_num [Fin.ext_iff] at he
    change triangleWeights _ _ _ (P.vertex (i + 1)) 2 = 0 at he
    linarith
  · rw [heq] at hj1
    have he := triangleWeights_vertices hdet 2 1
    norm_num [Fin.ext_iff] at he
    change triangleWeights _ _ _ (P.vertex (i - 1)) 1 = 0 at he
    linarith

theorem empty_corner_base_disjoint_carrier {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m)
    (i : ZMod (m + 3))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) :
    Disjoint (openSegment ℝ (P.vertex (i + 1)) (P.vertex (i - 1))) P.carrier := by
  have hdet : Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i - 1) - P.vertex i) ≠ 0 := by
    rw [Plane.det_comm]
    exact neg_ne_zero.mpr (P.corner i)
  have hbc : P.vertex (i + 1) ≠ P.vertex (i - 1) :=
    fun he ↦ PrePolygon.pred_ne_succ i (P.vertex_inj he).symm
  have hT := inside_eq_interior_of_convex_boundary (cornerTriangle P i).isSeparating_carrier
    ((finite_range (cornerTriangle P i).vertex).isCompact_convexHull ℝ).isClosed
    (convex_convexHull ℝ _) (triangle_carrier_subset_hull (cornerTriangle P i))
    (triangle_carrier_disjoint_interior_hull (cornerTriangle P i))
  rw [cornerTriangle_range] at hT
  have hthree : (3 : ZMod (m + 3)) ≠ 0 := by
    intro he
    have hd : m + 3 ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (m + 3)).mp he
    have := Nat.le_of_dvd (by omega : 0 < 3) hd
    omega
  refine disjoint_left.mpr ?_
  intro x hx hxP
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxP
  have hxopen : x ∈ openSegment ℝ (P.vertex j) (P.vertex (j + 1)) :=
    mem_openSegment_of_ne_left_right
      (fun he ↦ vertex_notMem_empty_corner_base P i hempty j (he ▸ hx))
      (fun he ↦ vertex_notMem_empty_corner_base P i hempty (j + 1) (he ▸ hx)) hxj
  have havoid : Disjoint (P.edge j) (interior (convexHull ℝ
      {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)})) := by
    rw [← hT]
    exact (empty_corner_triangle_disjoint_carrier P i hempty).symm.mono_left
      (ClosedPolygon.edge_subset_carrier (P := P) (i := j))
  have hbase := segment_base_subset_of_avoids_triangle hdet hbc hx hxopen
    (vertex_notMem_empty_corner_base P i hempty j)
    (vertex_notMem_empty_corner_base P i hempty (j + 1)) havoid
  have hend : ∀ k, P.vertex k ∈ P.edge j → k = j ∨ k = j + 1 := by
    intro k hk
    by_cases hkj : k = j
    · exact Or.inl hkj
    · have he := P.edges_meet j k (Ne.symm hkj) ⟨hk, left_mem_segment ℝ _ _⟩
      exact he.elim (fun he ↦ Or.inl (P.vertex_inj he)) (fun he ↦ Or.inr (P.vertex_inj he))
  have hb := hend (i + 1) (hbase (left_mem_segment ℝ _ _))
  have hc := hend (i - 1) (hbase (right_mem_segment ℝ _ _))
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact hbc (congrArg P.vertex (hb.trans hc.symm))
  · exact hthree (by linear_combination hb - hc)
  · exact ClosedPolygon.one_ne_zero' (m := m) (by linear_combination hb - hc)
  · exact hbc (congrArg P.vertex (hb.trans hc.symm))

theorem empty_corner_base_inside {m : ℕ} (P : ClosedPolygon m) (hm : 0 < m)
    (i : ZMod (m + 3)) (F : Plane →L[ℝ] ℝ)
    (hF : ∀ x ∈ P.carrier, F x ≤ F (P.vertex i))
    (hprev : F (P.vertex (i - 1)) < F (P.vertex i))
    (hnext : F (P.vertex (i + 1)) < F (P.vertex i))
    (hempty : ∀ j, P.vertex j ∈ convexHull ℝ (range (cornerTriangle P i).vertex) →
      j = i ∨ j = i + 1 ∨ j = i - 1) :
    openSegment ℝ (P.vertex (i + 1)) (P.vertex (i - 1)) ⊆ inside P.carrier := by
  have hclosed := (empty_corner_triangle_inside P i F hF hprev hnext hempty).2
  rw [triangle_closed_inside_eq_hull, cornerTriangle_range] at hclosed
  intro x hx
  have hxH : x ∈ convexHull ℝ {P.vertex i, P.vertex (i + 1), P.vertex (i - 1)} :=
    segment_subset_convexHull (by simp) (by simp) (openSegment_subset_segment ℝ _ _ hx)
  have hxcl := hclosed hxH
  rw [(IsRegionOf.inside P.carrier).closure_eq P.isSeparating_carrier] at hxcl
  exact hxcl.resolve_right (fun hxP ↦ disjoint_left.mp
    (empty_corner_base_disjoint_carrier P hm i hempty) hx hxP)

end Reeken.Geometry
