import Reeken.Geometry.SimpleLoop
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # From a circle embedding to the interval parametrization used by Reeken -/

open Set

namespace Reeken.Geometry

noncomputable def circleParam (t : ℝ) : Circle := Circle.exp ((2 * t - 1) * Real.pi)

theorem continuous_circleParam : Continuous circleParam := by
  apply Circle.exp.continuous.comp
  fun_prop

theorem circleParam_endpoint : circleParam 1 = circleParam 0 := by
  apply Circle.exp_eq_exp.mpr
  exact ⟨1, by norm_num; ring⟩

theorem circleParam_injOn : InjOn circleParam (Ico 0 1) := by
  intro a ha b hb hab
  have hangle := Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith)
  have ha' : (2 * a - 1) * Real.pi ∈ Ico (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos, ha.1, ha.2]
  have hb' : (2 * b - 1) * Real.pi ∈ Ico (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos, hb.1, hb.2]
  have he := mul_right_cancel₀ Real.pi_ne_zero (hangle ha' hb' hab)
  linarith

theorem circleParam_surjOn : SurjOn circleParam (Icc 0 1) univ := by
  intro z _
  let t := ((z : ℂ).arg / Real.pi + 1) / 2
  have hpi := Real.pi_pos
  have hlo := Complex.neg_pi_lt_arg (z : ℂ)
  have hhi := Complex.arg_le_pi (z : ℂ)
  have hlo' : -1 < (z : ℂ).arg / Real.pi := (lt_div_iff₀ hpi).mpr (by linarith)
  have hhi' : (z : ℂ).arg / Real.pi ≤ 1 := (div_le_iff₀ hpi).mpr (by linarith)
  refine ⟨t, ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, ?_⟩
  have ht : (2 * t - 1) * Real.pi = (z : ℂ).arg := by
    dsimp [t]
    field_simp
    ring
  rw [circleParam, ht, Circle.exp_arg]

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def SimpleLoop.ofCircle (r : Circle → E) (hc : Continuous r)
    (hi : Function.Injective r) : SimpleLoop E where
  toFun t := r (circleParam t)
  continuousOn := (hc.comp continuous_circleParam).continuousOn
  endpoint := congrArg r circleParam_endpoint
  injectiveOn := fun _ ha _ hb h ↦ circleParam_injOn ha hb (hi h)

theorem SimpleLoop.ofCircle_image (r : Circle → E) (hc : Continuous r)
    (hi : Function.Injective r) : (SimpleLoop.ofCircle r hc hi) '' Icc 0 1 = range r := by
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact mem_range_self _
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht, htz⟩ := circleParam_surjOn (mem_univ z)
    exact ⟨t, ht, congrArg r htz⟩

/-- The usual unit circle and the unit sphere in the real Euclidean plane agree
under the standard real-linear isometry from complex coordinates. -/
noncomputable def circlePlaneEquiv : Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr (z : ℂ), by
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using z.norm_coe⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z.val, by
    change Complex.orthonormalBasisOneI.repr.symm z.val ∈ Metric.sphere 0 1
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply _)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply _)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def SimpleLoop.ofPlaneCircle
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → E)
    (hc : Continuous r) (hi : Function.Injective r) : SimpleLoop E :=
  SimpleLoop.ofCircle (r ∘ circlePlaneEquiv) (hc.comp circlePlaneEquiv.continuous)
    (hi.comp circlePlaneEquiv.injective)

theorem SimpleLoop.ofPlaneCircle_image
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → E)
    (hc : Continuous r) (hi : Function.Injective r) :
    (SimpleLoop.ofPlaneCircle r hc hi) '' Icc 0 1 = range r := by
  rw [ofPlaneCircle, ofCircle_image]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact mem_range_self _
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := circlePlaneEquiv.surjective z
    exact mem_range_self w

end Reeken.Geometry
