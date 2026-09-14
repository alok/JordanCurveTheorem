import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Simple closed parametrized curves

The parameter endpoints represent the same point. Injectivity is required on `[0,1)`,
so the representation admits exactly the endpoint identification, not arbitrary repeated points.
-/

open Set

namespace Reeken.Geometry

variable (E : Type*) [TopologicalSpace E]

structure SimpleLoop where
  toFun : ℝ → E
  continuousOn : ContinuousOn toFun (Icc 0 1)
  endpoint : toFun 1 = toFun 0
  injectiveOn : InjOn toFun (Ico 0 1)

instance : CoeFun (SimpleLoop E) (fun _ ↦ ℝ → E) := ⟨SimpleLoop.toFun⟩

variable {E}

/-- The only failure of injectivity on the closed parameter interval is its two endpoints. -/
theorem SimpleLoop.eq_or_endpoints (f : SimpleLoop E) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : f a = f b) :
    a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  by_cases ha1 : a = 1
  · by_cases hb1 : b = 1
    · exact Or.inl (ha1.trans hb1.symm)
    · have hb0 : b = 0 := f.injectiveOn ⟨hb.1, lt_of_le_of_ne hb.2 hb1⟩
        ⟨le_rfl, zero_lt_one⟩ (by rw [← f.endpoint, ← ha1]; exact hab.symm)
      exact Or.inr (Or.inr ⟨ha1, hb0⟩)
  · by_cases hb1 : b = 1
    · have ha0 : a = 0 := f.injectiveOn ⟨ha.1, lt_of_le_of_ne ha.2 ha1⟩
        ⟨le_rfl, zero_lt_one⟩ (by rw [← f.endpoint, ← hb1]; exact hab)
      exact Or.inr (Or.inl ⟨ha0, hb1⟩)
    · exact Or.inl (f.injectiveOn ⟨ha.1, lt_of_le_of_ne ha.2 ha1⟩
        ⟨hb.1, lt_of_le_of_ne hb.2 hb1⟩ hab)

end Reeken.Geometry
