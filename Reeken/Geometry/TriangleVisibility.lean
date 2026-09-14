import Reeken.Geometry.RayExit
import Reeken.Geometry.TriangleContraction

/-! # Visibility through a triangle

A segment with endpoints outside a closed triangle or on its designated base which meets its interior
must cross one of the two sides adjacent to any designated vertex. A supporting
height excludes the opposite side from a suitably chosen first crossing.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem segment_crosses_triangle_side {a b c p q z : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0)
    (hp : p ∈ convexHull ℝ {a, b, c} → p ∈ segment ℝ b c)
    (hq : q ∈ convexHull ℝ {a, b, c} → q ∈ segment ℝ b c)
    (hz : z ∈ inside (Schoenflies.triangle h).carrier) (hzseg : z ∈ segment ℝ p q) :
    ∃ x ∈ segment ℝ p q, x ∈ segment ℝ a b ∪ segment ℝ c a ∧ x ≠ p ∧ x ≠ q := by
  let T := Schoenflies.triangle h
  have hclosed : closure (inside T.carrier) = convexHull ℝ {a, b, c} := by
    rw [triangle_closed_inside_eq_hull T, triangle_range_vertices h]
  have hrot : Plane.det (c - b) (a - b) ≠ 0 := by
    have he : Plane.det (c - b) (a - b) = Plane.det (b - a) (c - a) := by
      simp [Plane.det]
      ring
    rwa [he]
  obtain ⟨F, hFc, hFa⟩ := exists_triangle_edge_height hrot
  have hFK : ∀ x ∈ convexHull ℝ {a, b, c}, F x ≤ F b := by
    change convexHull ℝ {a, b, c} ⊆ {x | F x ≤ F b}
    apply convexHull_min
    · simp only [insert_subset_iff, singleton_subset_iff]
      change F a ≤ F b ∧ F b ≤ F b ∧ F c ≤ F b
      exact ⟨by linarith, le_rfl, hFc.le⟩
    · exact convex_halfSpace_le (show IsLinearMap ℝ F from ⟨F.map_add, F.map_smul⟩) (F b)
  have hzK : z ∈ interior (convexHull ℝ {a, b, c}) := by
    have hsub : inside T.carrier ⊆ convexHull ℝ {a, b, c} := by
      rw [← hclosed]
      exact subset_closure
    exact interior_maximal hsub T.isSeparating_carrier.isOpen_inside hz
  have hFz : F z < F b := by
    apply lt_of_le_of_ne (hFK z (interior_subset hzK))
    intro he
    exact notMem_interior_of_support F hFK he
      (by rw [map_sub, hFa]; linarith : 0 < F (b - a)) hzK
  have hbase : ∀ x ∈ segment ℝ b c, F x = F b := by
    rintro x ⟨u, v, hu, hv, huv, rfl⟩
    simp only [map_add, map_smul, smul_eq_mul, hFc]
    rw [← add_mul, huv, one_mul]
  have hend : ∀ r, (r ∈ convexHull ℝ {a, b, c} → r ∈ segment ℝ b c) →
      F r ≤ F z → r ∉ closure (inside T.carrier) := by
    intro r hr hFr hrC
    have he := hbase r (hr (hclosed ▸ hrC))
    rw [he] at hFr
    exact hFz.not_ge hFr
  obtain ⟨x, hxT, hxseg, hFx⟩ := exists_boundary_hit_below T.isSeparating_carrier F
    (hend p hp) (hend q hq) hz hzseg
  have hxK : x ∈ convexHull ℝ {a, b, c} := by
    rw [← hclosed]
    exact frontier_subset_closure (T.isSeparating_carrier.frontier_inside.symm ▸ hxT)
  have hxnotbase : x ∉ segment ℝ b c := fun hxbase ↦ hFz.not_ge (hbase x hxbase ▸ hFx)
  refine ⟨x, hxseg, ?_, ?_, ?_⟩
  rotate_left
  · rintro rfl
    exact hxnotbase (hp hxK)
  · rintro rfl
    exact hxnotbase (hq hxK)
  rw [triangle_carrier_eq_segments h] at hxT
  rcases hxT with (hx | hx) | hx
  · exact Or.inl hx
  · exact False.elim (hxnotbase hx)
  · exact Or.inr hx

end Reeken.Geometry
