import Reeken.Geometry.ConvexEnclosure
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! # The triangle base case

Every three-vertex simple polygon has convex closed inside and is contractible.
The supporting-line calculation handles either orientation of the vertices.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem segment_disjoint_interior_triangle {a b c : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) :
    Disjoint (segment ℝ a b) (interior (convexHull ℝ {a, b, c})) := by
  let D := Plane.det (b - a) (c - a)
  let L : Plane →L[ℝ] ℝ := {
    toFun := Plane.det (b - a)
    map_add' := Plane.det_add_right (b - a)
    map_smul' := by intro t x; simp
    cont := Plane.continuous_det_right (b - a)
  }
  let F : Plane →L[ℝ] ℝ := (-D⁻¹) • L
  have hv : F (a - c) = 1 := by
    change -D⁻¹ * Plane.det (b - a) (a - c) = 1
    have he : Plane.det (b - a) (a - c) = -D := by
      dsimp [D, Plane.det]
      ring
    rw [he]
    field_simp [show D ≠ 0 from h]
  have hba : F b = F a := by
    have he : F (b - a) = 0 := by change -D⁻¹ * Plane.det (b - a) (b - a) = 0; simp
    rw [map_sub, sub_eq_zero] at he
    exact he
  have hca : F c = F a - 1 := by rw [map_sub] at hv; linarith
  have hK : ∀ x ∈ convexHull ℝ {a, b, c}, F x ≤ F a := by
    change convexHull ℝ {a, b, c} ⊆ {x | F x ≤ F a}
    apply convexHull_min
    · simp only [insert_subset_iff, singleton_subset_iff]
      change F a ≤ F a ∧ F b ≤ F a ∧ F c ≤ F a
      exact ⟨le_rfl, hba.le, by linarith⟩
    · exact convex_halfSpace_le (show IsLinearMap ℝ F from ⟨F.map_add, F.map_smul⟩) (F a)
  refine disjoint_left.mpr ?_
  rintro x ⟨u, v, hu, hv', huv, rfl⟩
  have hx : F (u • a + v • b) = F a := by
    simp only [map_add, map_smul, smul_eq_mul, hba]
    rw [← add_mul, huv, one_mul]
  exact notMem_interior_of_support F hK hx (by rw [hv]; norm_num)

/-- The polygon's three edges lie on the boundary of their convex hull. -/
theorem triangle_carrier_disjoint_interior_hull (P : ClosedPolygon 0) :
    Disjoint P.carrier (interior (convexHull ℝ (range P.vertex))) := by
  have hr : ∀ i : ZMod 3, range P.vertex =
      {P.vertex i, P.vertex (i + 1), P.vertex (i + 2)} := by
    intro i
    have hi : ∀ j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2 := by
      intro j
      have hcases : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      have hj := hcases (j - i)
      rcases hj with hj | hj | hj
      · exact Or.inl (sub_eq_zero.mp hj)
      · right; left; linear_combination hj
      · right; right; linear_combination hj
    ext x
    simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rcases hi j with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [ClosedPolygon.carrier, disjoint_iUnion_left]
  intro i
  rw [hr i]
  apply segment_disjoint_interior_triangle
  have he : i - 1 = i + 2 := by fin_cases i <;> decide
  have hc := P.corner i
  rw [he, Plane.det_comm] at hc
  exact neg_ne_zero.mp hc

theorem triangle_carrier_subset_hull (P : ClosedPolygon 0) :
    P.carrier ⊆ convexHull ℝ (range P.vertex) := by
  rintro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact segment_subset_convexHull (mem_range_self i) (mem_range_self (i + 1)) hi

theorem triangle_closed_inside_eq_hull (P : ClosedPolygon 0) :
    closure (inside P.carrier) = convexHull ℝ (range P.vertex) :=
  closure_inside_eq_of_convex_boundary P.isSeparating_carrier
    ((finite_range P.vertex).isCompact_convexHull ℝ).isClosed
    (convex_convexHull ℝ _) (triangle_carrier_subset_hull P)
    (triangle_carrier_disjoint_interior_hull P)

/-- The base case of finite polygon contraction, for every nondegenerate triangle. -/
theorem contractibleSpace_triangle_closed_inside (P : ClosedPolygon 0) :
    ContractibleSpace (closure (inside P.carrier)) := by
  rw [triangle_closed_inside_eq_hull P]
  exact (convex_convexHull ℝ _).contractibleSpace
    ((range_nonempty P.vertex).mono (subset_convexHull ℝ _))

/-- Every loop in an open triangular inside contracts there. -/
theorem isSimplyConnected_triangle_inside (P : ClosedPolygon 0) :
    IsSimplyConnected (inside P.carrier) := by
  have he := inside_eq_interior_of_convex_boundary P.isSeparating_carrier
    ((finite_range P.vertex).isCompact_convexHull ℝ).isClosed
    (convex_convexHull ℝ _) (triangle_carrier_subset_hull P)
    (triangle_carrier_disjoint_interior_hull P)
  have hconv : Convex ℝ (inside P.carrier) := by rw [he]; exact (convex_convexHull ℝ _).interior
  let := hconv.contractibleSpace P.isSeparating_carrier.isConnected_inside.nonempty
  exact SimplyConnectedSpace.ofContractible _

end Reeken.Geometry
