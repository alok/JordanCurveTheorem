import Reeken.Geometry.PolygonEar
import Reeken.Geometry.TruncatedTriangle

/-! # A corner triangle with no vertices above its base

The two sides may stop before the polygon's neighboring vertices. If every other
polygon vertex in the closed triangle is on its base, the triangle interior is
free of the polygon. This is the visibility criterion for a maximal-height vertex.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem inside_triangle_eq_interior_hull (T : ClosedPolygon 0) :
    inside T.carrier = interior (convexHull ℝ (range T.vertex)) :=
  inside_eq_interior_of_convex_boundary T.isSeparating_carrier
    ((finite_range T.vertex).isCompact_convexHull ℝ).isClosed (convex_convexHull ℝ _)
    (triangle_carrier_subset_hull T) (triangle_carrier_disjoint_interior_hull T)

theorem corner_triangle_disjoint_carrier_of_vertices_on_base {m : ℕ}
    (P : ClosedPolygon m) (i : ZMod (m + 3)) {b c : Plane}
    (hb : b ∈ segment ℝ (P.vertex i) (P.vertex (i + 1)))
    (hc : c ∈ segment ℝ (P.vertex (i - 1)) (P.vertex i))
    (hdet : Plane.det (b - P.vertex i) (c - P.vertex i) ≠ 0)
    (hvertices : ∀ j, j ≠ i → P.vertex j ∈ convexHull ℝ {P.vertex i, b, c} →
      P.vertex j ∈ segment ℝ b c) :
    Disjoint (inside (Schoenflies.triangle hdet).carrier) P.carrier := by
  let T := Schoenflies.triangle hdet
  let A := cornerTriangle P i
  have hs : convexHull ℝ {P.vertex i, b, c} ⊆ convexHull ℝ (range A.vertex) := by
    rw [cornerTriangle_range]
    apply convexHull_min _ (convex_convexHull ℝ _)
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨subset_convexHull ℝ _ (by simp),
      segment_subset_convexHull (by simp) (by simp) hb,
      segment_subset_convexHull (by simp) (by simp) hc⟩
  have hsmall : inside T.carrier ⊆ inside A.carrier := by
    rw [inside_triangle_eq_interior_hull, inside_triangle_eq_interior_hull, triangle_range_vertices]
    exact interior_mono hs
  have hsideb : segment ℝ (P.vertex i) b ⊆ P.edge i :=
    (convex_segment (P.vertex i) (P.vertex (i + 1))).segment_subset (left_mem_segment ℝ _ _) hb
  have hsidec : segment ℝ c (P.vertex i) ⊆ P.edge (i - 1) := by
    change segment ℝ c (P.vertex i) ⊆ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
    rw [sub_add_cancel]
    exact (convex_segment (P.vertex (i - 1)) (P.vertex i)).segment_subset hc (right_mem_segment ℝ _ _)
  refine disjoint_left.mpr ?_
  intro z hz hzP
  obtain ⟨j, hzj⟩ := mem_iUnion.mp hzP
  have hji : j ≠ i := by
    rintro rfl
    exact (hsmall hz).1 (ClosedPolygon.edge_subset_carrier (P := A) (i := 0) hzj)
  have hjprev : j ≠ i - 1 := by
    intro he
    have hzedge : z ∈ A.edge 2 := by
      change z ∈ segment ℝ (P.vertex (i - 1)) (P.vertex i)
      rw [he] at hzj
      simpa only [ClosedPolygon.edge, sub_add_cancel] using hzj
    exact (hsmall hz).1 (ClosedPolygon.edge_subset_carrier hzedge)
  have hnexti : j + 1 ≠ i := fun he ↦ hjprev (by linear_combination he)
  obtain ⟨x, hxj, hxside, hxp, hxq⟩ := segment_crosses_triangle_side hdet
    (hvertices j hji) (hvertices (j + 1) hnexti) hz hzj
  have hxends : x ∈ ({P.vertex j, P.vertex (j + 1)} : Set Plane) := by
    rcases hxside with hxb | hxc
    · exact P.edges_meet j i hji ⟨hxj, hsideb hxb⟩
    · exact P.edges_meet j (i - 1) hjprev ⟨hxj, hsidec hxc⟩
  exact hxends.elim hxp hxq

end Reeken.Geometry
