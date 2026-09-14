import Reeken.Geometry.ExteriorBounds
import Schoenflies.Strip

/-! # A small boundary cannot enclose a distant point

These estimates apply to the bounded complementary components of any planar set.
They use the connected exterior of a square, without a Jordan-curve assumption.
The translated form is needed for the infinitesimal crosscut barriers in Lemma 3.
-/

open Set Metric Schoenflies

namespace Reeken.Geometry

theorem inside_subset_closedSquare_center {C : Set Plane} {a : Plane} {r : ℝ}
    (hC : C ⊆ Plane.closedSquare a r) : inside C ⊆ Plane.closedSquare a r := by
  let S := (fun w : Plane ↦ w + a) '' Plane.beyondSquare r
  have hS : IsPreconnected S := (Plane.isConnected_beyondSquare r).isPreconnected.image _
    (continuous_id.add continuous_const).continuousOn
  have hsub : S ⊆ Cᶜ := by
    rintro x ⟨w, hw, rfl⟩ hx
    have hx' := hC hx
    have hw' : w ∉ Plane.closedSquare 0 r := by rwa [Plane.beyondSquare_eq_compl] at hw
    apply hw'
    simpa only [Plane.closedSquare, mem_ofPred_eq, Plane.supDist, add_sub_cancel_right,
      sub_zero] using hx'
  have hunbounded : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    apply not_isBounded_beyondSquare r
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R + ‖a‖, fun w hw ↦ ?_⟩
    have h := norm_sub_le (w + a) a
    rw [add_sub_cancel_right] at h
    exact h.trans (by linarith [hR (w + a) (mem_image_of_mem _ hw)])
  intro x hx
  by_contra hn
  have hxS : x ∈ S := by
    refine ⟨x - a, ?_, sub_add_cancel _ _⟩
    rw [Plane.beyondSquare_eq_compl]
    simpa only [Plane.closedSquare, mem_compl_iff, mem_ofPred_eq, Plane.supDist, sub_zero] using hn
  exact hunbounded (hx.2.subset (hS.subset_connectedComponentIn hxS hsub))

theorem dist_le_of_mem_inside_of_boundary_dist_le {C : Set Plane} {a x : Plane} {r : ℝ}
    (hC : ∀ y ∈ C, dist y a ≤ r) (hx : x ∈ inside C) :
    dist x a ≤ Real.sqrt 2 * r := by
  have hCs : C ⊆ Plane.closedSquare a r := by
    intro y hy
    exact (Plane.supNorm_le_norm (y - a)).trans (by simpa only [dist_eq_norm] using hC y hy)
  have hxS := inside_subset_closedSquare_center hCs hx
  change Plane.supNorm (x - a) ≤ r at hxS
  rw [dist_eq_norm]
  exact (Plane.norm_le_sqrt_two_mul_supNorm (x - a)).trans
    (mul_le_mul_of_nonneg_left hxS (Real.sqrt_nonneg _))

theorem polygon_carrier_subset_of_vertices {m : ℕ} (Q : ClosedPolygon m) {D : Set Plane}
    (hD : Convex ℝ D) (hvertices : ∀ j, Q.vertex j ∈ D) : Q.carrier ⊆ D := by
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact hD.segment_subset (hvertices j) (hvertices (j + 1)) hj

/-- If all corner connections end at one nearby foot, the whole inner polygon is
small, so its inside is small too. This includes the degenerate ring case. -/
theorem dist_le_of_common_corner_foot {m : ℕ} (Q : ClosedPolygon m) {a x : Plane} {r : ℝ}
    (hvertices : ∀ j, dist (Q.vertex j) a ≤ r) (hx : x ∈ inside Q.carrier) :
    dist x a ≤ Real.sqrt 2 * r :=
  dist_le_of_mem_inside_of_boundary_dist_le
    (fun _ hy ↦ polygon_carrier_subset_of_vertices Q (convex_closedBall a r) hvertices hy) hx

end Reeken.Geometry
