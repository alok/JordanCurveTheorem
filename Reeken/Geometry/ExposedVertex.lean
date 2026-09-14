import Reeken.Geometry.ConvexEnclosure
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # A strictly exposed polygon vertex

A vertex of maximal norm has a supporting line which contains no other vertex.
The strict inequality follows from the squared distance between distinct vertices.
No generic-position perturbation of the polygon is required.
-/

open Set Schoenflies

namespace Reeken.Geometry

/-- Every finite simple polygon has a linear height with a unique highest vertex. -/
theorem exists_strictly_exposed_vertex {m : ℕ} (P : ClosedPolygon m) :
    ∃ (i : ZMod (m + 3)) (F : Plane →L[ℝ] ℝ),
      (∀ j, j ≠ i → F (P.vertex j) < F (P.vertex i)) ∧
      (∀ x ∈ P.carrier, F x ≤ F (P.vertex i)) ∧
      (∀ x ∈ closure (inside P.carrier), F x ≤ F (P.vertex i)) := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j ↦ ‖P.vertex j‖) Finset.univ_nonempty
  let F : Plane →L[ℝ] ℝ := innerSL ℝ (P.vertex i)
  have hstrict : ∀ j, j ≠ i → F (P.vertex j) < F (P.vertex i) := by
    intro j hji
    have hnorm := hmax j (Finset.mem_univ j)
    have hnormsq : ‖P.vertex j‖ ^ 2 ≤ ‖P.vertex i‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hdist : 0 < ‖P.vertex i - P.vertex j‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun he ↦ hji (P.vertex_inj he).symm)))
    change inner ℝ (P.vertex i) (P.vertex j) < inner ℝ (P.vertex i) (P.vertex i)
    rw [real_inner_self_eq_norm_sq]
    have hd := norm_sub_sq_real (P.vertex i) (P.vertex j)
    nlinarith
  have hle : ∀ j, F (P.vertex j) ≤ F (P.vertex i) := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · exact (hstrict j hji).le
  have hcarrier : ∀ x ∈ P.carrier, F x ≤ F (P.vertex i) := by
    rintro x hx
    obtain ⟨j, u, v, hu, hv, huv, rfl⟩ := mem_iUnion.mp hx
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      u * F (P.vertex j) + v * F (P.vertex (j + 1)) ≤
          u * F (P.vertex i) + v * F (P.vertex i) := by gcongr <;> exact hle _
      _ = F (P.vertex i) := by rw [← add_mul, huv, one_mul]
  refine ⟨i, F, hstrict, hcarrier, ?_⟩
  have hv : 0 < F (P.vertex i - P.vertex (i + 1)) := by
    rw [map_sub]
    exact sub_pos.mpr (hstrict (i + 1) (ClosedPolygon.succ_ne_self i))
  have hsub := inside_subset_halfSpace F (F (P.vertex i)) hv hcarrier
  exact closure_minimal hsub (isClosed_le F.continuous continuous_const)

/-- The sum of two independent rays and its negative lie in opposite sectors. -/
theorem sum_neg_sum_opposite_arcs {u v : Plane} (h : Plane.det u v ≠ 0) :
    (u + v ∈ Plane.arcCCW u v ∧ -(u + v) ∈ Plane.arcCCW v u) ∨
      (u + v ∈ Plane.arcCCW v u ∧ -(u + v) ∈ Plane.arcCCW u v) := by
  have hs₁ : Plane.det u (u + v) = Plane.det u v := by simp [Plane.det_add_right]
  have hs₂ : Plane.det (u + v) v = Plane.det u v := by simp [Plane.det_add_left]
  have hn₁ : Plane.det u (-(u + v)) = -Plane.det u v := by
    simp [Plane.det]
    ring
  have hn₂ : Plane.det (-(u + v)) v = -Plane.det u v := by
    simp [Plane.det]
    ring
  rcases lt_or_gt_of_ne h with hneg | hpos
  · right
    have hp : 0 < Plane.det v u := by rw [Plane.det_comm]; linarith
    constructor
    · apply (Plane.mem_arcCCW_iff hp).mpr
      constructor <;> rw [Plane.det_comm]
      · rw [hs₂]; linarith
      · rw [hs₁]; linarith
    · exact (Plane.mem_arcCCW_rev_iff hp).mpr (Or.inl (by rw [Plane.det_comm, hn₂]; linarith))
  · left
    exact ⟨(Plane.mem_arcCCW_iff hpos).mpr ⟨hs₁ ▸ hpos, hs₂ ▸ hpos⟩,
      (Plane.mem_arcCCW_rev_iff hpos).mpr (Or.inl (by rw [hn₁]; linarith))⟩

/-- At a strictly exposed vertex the inward bisector enters the bounded region.
This supplies an actual interior direction for constructing a diagonal. -/
theorem exists_inward_bisector {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3))
    (F : Plane →L[ℝ] ℝ) (hF : ∀ x ∈ P.carrier, F x ≤ F (P.vertex i))
    (hprev : F (P.vertex (i - 1)) < F (P.vertex i))
    (hnext : F (P.vertex (i + 1)) < F (P.vertex i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      P.vertex i + ε • (P.tang i + P.rayIn i) ∈ inside P.carrier := by
  obtain ⟨D⟩ := exists_stripData P
  have hR := D.R_pos
  let d := P.tang i + P.rayIn i
  have hFt : F (P.tang i) < 0 := by
    change F (‖P.vertex (i + 1) - P.vertex i‖⁻¹ • (P.vertex (i + 1) - P.vertex i)) < 0
    rw [map_smul, map_sub, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr
      (ClosedPolygon.sub_ne_zero_of_edge (P := P) (i := i))))
      (sub_neg.mpr hnext)
  have hFr : F (P.rayIn i) < 0 := by
    change F (‖P.vertex (i - 1) - P.vertex i‖⁻¹ • (P.vertex (i - 1) - P.vertex i)) < 0
    rw [map_smul, map_sub, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr
      (ClosedPolygon.vertex_pred_ne (P := P) (i := i))))
      (sub_neg.mpr hprev)
  have hFd : F d < 0 := by change F (P.tang i + P.rayIn i) < 0; rw [map_add]; linarith
  refine ⟨D.R / (‖d‖ + 1), by positivity, ?_⟩
  intro ε hε hεδ
  have hsmall : ε * ‖d‖ < D.R := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < ‖d‖ + 1)).mp hεδ
    nlinarith
  let x := P.vertex i + ε • d
  let z := P.vertex i + ε • (-d)
  have hxb : x ∈ Metric.ball (P.vertex i) D.R := by
    simpa [x, dist_eq_norm, norm_smul, abs_of_pos hε] using hsmall
  have hzb : z ∈ Metric.ball (P.vertex i) D.R := by
    simpa [z, dist_eq_norm, norm_smul, abs_of_pos hε] using hsmall
  have hsectors : (x ∈ D.sideL ∧ z ∈ D.sideR) ∨ (x ∈ D.sideR ∧ z ∈ D.sideL) := by
    have hd : Plane.det (P.tang i) (P.rayIn i) ≠ 0 := by
      rw [Plane.det_comm]
      exact neg_ne_zero.mpr (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))
    have hsideL : ∀ w ∈ Plane.arcCCW (P.tang i) (P.rayIn i),
        P.vertex i + ε • w ∈ Metric.ball (P.vertex i) D.R →
        P.vertex i + ε • w ∈ D.sideL := by
      intro w hw hwb
      refine mem_iUnion.mpr ⟨i, Or.inl ⟨?_, hwb⟩⟩
      change P.vertex i + ε • w - P.vertex i ∈ Plane.arcCCW (P.tang i) (P.rayIn i)
      rw [add_sub_cancel_left]
      exact (Plane.smul_mem_arcCCW hε).mpr hw
    have hsideR : ∀ w ∈ Plane.arcCCW (P.rayIn i) (P.tang i),
        P.vertex i + ε • w ∈ Metric.ball (P.vertex i) D.R →
        P.vertex i + ε • w ∈ D.sideR := by
      intro w hw hwb
      refine mem_iUnion.mpr ⟨i, Or.inl ⟨?_, hwb⟩⟩
      change P.vertex i + ε • w - P.vertex i ∈ Plane.arcCCW (P.rayIn i) (P.tang i)
      rw [add_sub_cancel_left]
      exact (Plane.smul_mem_arcCCW hε).mpr hw
    rcases sum_neg_sum_opposite_arcs hd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hsideL d h₁ hxb, hsideR (-d) h₂ hzb⟩
    · exact Or.inr ⟨hsideR d h₁ hxb, hsideL (-d) h₂ hzb⟩
  have hzx : F (P.vertex i) < F z := by
    dsimp [z]
    rw [map_add, map_smul, map_neg, smul_eq_mul]
    nlinarith
  have hznot : z ∉ inside P.carrier := by
    have hv : 0 < F (-d) := by rw [map_neg]; linarith
    exact fun hz ↦ hzx.not_ge (inside_subset_halfSpace F (F (P.vertex i)) hv hF hz)
  have hxC : x ∉ P.carrier := hsectors.elim
    (fun hs ↦ ClosedPolygon.sideL_subset_compl D hs.1)
    (fun hs ↦ ClosedPolygon.sideR_subset_compl D hs.1)
  have hzC : z ∉ P.carrier := hsectors.elim
    (fun hs ↦ ClosedPolygon.sideR_subset_compl D hs.2)
    (fun hs ↦ ClosedPolygon.sideL_subset_compl D hs.2)
  have hzout : z ∈ outside P.carrier :=
    (show z ∈ inside P.carrier ∪ outside P.carrier by rwa [inside_union_outside]).resolve_left hznot
  have hne : connectedComponentIn P.carrierᶜ x ≠ connectedComponentIn P.carrierᶜ z := by
    rcases hsectors with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · exact P.connectedComponentIn_ne_of_mem_sides D hx hz
    · exact Ne.symm (P.connectedComponentIn_ne_of_mem_sides D hz hx)
  have hxregions : x ∈ inside P.carrier ∪ outside P.carrier := by rwa [inside_union_outside]
  exact hxregions.resolve_right (fun hxout ↦ hne (by
    rw [P.isSeparating_carrier.connectedComponentIn_eq_outside hxout,
      P.isSeparating_carrier.connectedComponentIn_eq_outside hzout]))

/-- An actual inward-pointing corner exists for every finite simple polygon. -/
theorem exists_vertex_inward_bisector {m : ℕ} (P : ClosedPolygon m) :
    ∃ (i : ZMod (m + 3)) (δ : ℝ), 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      P.vertex i + ε • (P.tang i + P.rayIn i) ∈ inside P.carrier := by
  obtain ⟨i, F, hstrict, hcarrier, _⟩ := exists_strictly_exposed_vertex P
  have hprev : i - 1 ≠ i := fun he ↦
    ClosedPolygon.one_ne_zero' (m := m) (sub_eq_self.mp he)
  obtain ⟨δ, hδ, h⟩ := exists_inward_bisector P i F hcarrier
    (hstrict (i - 1) hprev) (hstrict (i + 1) (ClosedPolygon.succ_ne_self i))
  exact ⟨i, δ, hδ, h⟩

end Reeken.Geometry
