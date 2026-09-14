import Reeken.Nonstandard.PolygonApproximation
import Reeken.Geometry.UniformPolygon

/-! # Construction of the initial infinitesimal inscribed polygon -/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E]

theorem uniform_maxEdge_small (f : SimpleLoop E) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in hyperfilter ℕ, (InscribedPolygon.uniform f n).maxEdge < ε := by
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous f.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [Nat.hyperfilter_le_atTop (eventually_ge_atTop N)] with n hn
  apply (Finset.sup'_lt_iff _).mpr
  intro j _
  rw [InscribedPolygon.uniform_edgeLength f n j]
  have hl := meshTime_mem (n + 2) j (Nat.le_of_lt j.isLt)
  have hr := meshTime_mem (n + 2) (j + 1) (Nat.succ_le_of_lt j.isLt)
  apply hd _ hl _ hr
  rw [meshTime_dist_step]
  have hcount : N + 1 ≤ n + 2 + 1 := by omega
  exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hcount)).trans_lt hN

variable [NormedSpace ℝ E]

/-- The explicit equally sampled polygons form an admissible infinitesimal approximation.
This theorem makes no simplicity claim; that is the subsequent loop-cutting step. -/
theorem exists_initial_polygon (f : SimpleLoop E) :
    ∃ p : ℕ → InscribedPolygon f,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in hyperfilter ℕ, (p n).maxEdge < ε) ∧
      shadow (fun n ↦ (p n).trace) = f '' Icc 0 1 :=
  ⟨InscribedPolygon.uniform f, uniform_maxEdge_small f,
    shadow_polygon (InscribedPolygon.uniform f) (uniform_maxEdge_small f)⟩

end Reeken.NSA
