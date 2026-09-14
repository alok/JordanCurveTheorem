import Reeken.Geometry.EnclosedSets
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Contractible

/-! # Convex enclosures of separating polygonal curves

A supporting half-plane bounds every bounded complementary component. If a
separating curve lies on the boundary of a closed convex set, its closed inside
is that convex set. This supplies the convex base case of polygon contraction.
-/

open Set Schoenflies

namespace Reeken.Geometry

/-- A nonconstant linear functional has an unbounded strict upper half-plane. -/
theorem not_isBounded_halfSpace (F : Plane →L[ℝ] ℝ) (c : ℝ)
    {v : Plane} (hv : 0 < F v) :
    ¬ Bornology.IsBounded {x | c < F x} := by
  intro hb
  obtain ⟨R, hR⟩ := (F.lipschitz.isBounded_image hb).exists_norm_le
  let t := (max c R + 1) / F v
  have he : F (t • v) = max c R + 1 := by
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ (ne_of_gt hv)
  have hx : t • v ∈ {x | c < F x} := by
    change c < F (t • v)
    rw [he]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have h := hR (F (t • v)) (mem_image_of_mem F hx)
  rw [he, Real.norm_eq_abs] at h
  linarith [le_abs_self (max c R + 1), le_max_right c R]

/-- Supporting half-planes also contain the bounded complementary components. -/
theorem inside_subset_halfSpace {C : Set Plane} (F : Plane →L[ℝ] ℝ) (c : ℝ)
    {v : Plane} (hv : 0 < F v) (hC : ∀ x ∈ C, F x ≤ c) :
    inside C ⊆ {x | F x ≤ c} := by
  intro x hx
  by_contra h
  change ¬ F x ≤ c at h
  have hxH : x ∈ {y | c < F y} := by exact lt_of_not_ge h
  have hsub : {y | c < F y} ⊆ Cᶜ := fun y hy hCy ↦ (hC y hCy).not_gt hy
  have hconn : IsPreconnected {y | c < F y} :=
    (convex_halfSpace_gt (show IsLinearMap ℝ F from ⟨F.map_add, F.map_smul⟩) c).isPreconnected
  exact not_isBounded_halfSpace F c hv
    (hx.2.subset (hconn.subset_connectedComponentIn hxH hsub))

/-- A closed convex set containing a nonempty curve contains all of its bounded
complementary components. Separation supplies a supporting half-plane at each
point outside the convex set. -/
theorem inside_subset_closed_convex {C K : Set Plane} (hne : K.Nonempty)
    (hK : IsClosed K) (hconv : Convex ℝ K) (hCK : C ⊆ K) : inside C ⊆ K := by
  intro x hx
  by_contra hxK
  obtain ⟨F, c, hFK, hFx⟩ := geometric_hahn_banach_closed_point hconv hK hxK
  obtain ⟨y, hy⟩ := hne
  have hv : 0 < F (x - y) := by
    rw [map_sub]
    linarith [hFK y hy]
  exact hFx.not_ge (inside_subset_halfSpace F c hv (fun z hz ↦ (hFK z (hCK hz)).le) hx)

/-- If a separating curve lies on the boundary of a closed convex set, the
ordinary inside is exactly its interior. -/
theorem inside_eq_interior_of_convex_boundary {C K : Set Plane}
    (hC : IsSeparating C) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hCK : C ⊆ K) (hdisj : Disjoint C (interior K)) : inside C = interior K := by
  have hne : K.Nonempty := hC.isJordanCurve.nonempty.mono hCK
  have hsub : inside C ⊆ interior K :=
    interior_maximal (inside_subset_closed_convex hne hK hconv hCK) hC.isOpen_inside
  refine subset_antisymm hsub ?_
  obtain ⟨x, hx⟩ := hC.isConnected_inside.nonempty
  have hcomp : interior K ⊆ Cᶜ := disjoint_left.mp hdisj.symm
  have h := hconv.interior.isPreconnected.subset_connectedComponentIn (hsub hx) hcomp
  rwa [hC.connectedComponentIn_eq_inside hx] at h

theorem closure_inside_eq_of_convex_boundary {C K : Set Plane}
    (hC : IsSeparating C) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hCK : C ⊆ K) (hdisj : Disjoint C (interior K)) : closure (inside C) = K := by
  have he := inside_eq_interior_of_convex_boundary hC hK hconv hCK hdisj
  have hne : (interior K).Nonempty := he ▸ hC.isConnected_inside.nonempty
  rw [he, hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.closure_eq]

theorem contractibleSpace_closed_inside_of_convex_boundary {C K : Set Plane}
    (hC : IsSeparating C) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hCK : C ⊆ K) (hdisj : Disjoint C (interior K)) :
    ContractibleSpace (closure (inside C)) := by
  rw [closure_inside_eq_of_convex_boundary hC hK hconv hCK hdisj]
  exact hconv.contractibleSpace (hC.isJordanCurve.nonempty.mono hCK)

/-- A point on a genuine supporting line cannot be an interior point. -/
theorem notMem_interior_of_support {K : Set Plane} (F : Plane →L[ℝ] ℝ)
    {c : ℝ} (hK : ∀ z ∈ K, F z ≤ c) {x v : Plane} (hx : F x = c)
    (hv : 0 < F v) : x ∉ interior K := by
  intro hxi
  have ht : Filter.Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
    convert (show Continuous (fun t : ℝ ↦ x + t • v) by fun_prop).tendsto 0 using 1; simp
  obtain ⟨t, ht0, htK⟩ := (ht.eventually_mem (mem_interior_iff_mem_nhds.mp hxi)).exists_gt
  have h := hK (x + t • v) htK
  rw [map_add, map_smul, smul_eq_mul, hx] at h
  nlinarith

end Reeken.Geometry
