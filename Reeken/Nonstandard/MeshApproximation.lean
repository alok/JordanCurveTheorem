import Reeken.Nonstandard.Approximation
import Reeken.Geometry.UniformMesh

/-!
# An internal inscribed mesh has exactly the curve as its shadow

This constructs the initial approximation in Kanovei–Reeken Lemma 2. The mesh is
not yet simple; removing crossings while preserving approximation is a separate step.
-/

open Filter Set

namespace Reeken.NSA

open Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The internal union of sampled segments has exactly the parametrized curve as its shadow. -/
theorem shadow_meshTrace {f : ℝ → E} (hf : ContinuousOn f (Icc 0 1)) :
    shadow (meshTrace f) = f '' Icc 0 1 := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  have happ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in hyperfilter ℕ,
      (∀ x ∈ meshTrace f n, ∃ y ∈ f '' Icc 0 1, dist x y < ε) ∧
      (∀ y ∈ f '' Icc 0 1, ∃ x ∈ meshTrace f n, dist x y < ε) := by
    intro ε hε
    obtain ⟨N, hN⟩ := meshTrace_approximates hu hε
    exact Nat.hyperfilter_le_atTop (eventually_atTop.mpr ⟨N, hN⟩)
  apply shadow_eq_of_approximation (isCompact_Icc.image_of_continuousOn hf).isClosed
  · exact fun ε hε ↦ (happ ε hε).mono fun _ h ↦ h.1
  · exact fun ε hε ↦ (happ ε hε).mono fun _ h ↦ h.2

omit [NormedSpace ℝ E] in
/-- Every edge has infinitesimally close endpoints, uniformly in the internal edge index. -/
theorem mesh_edge_near {f : ℝ → E} (hf : ContinuousOn f (Icc 0 1)) (k : ℕ → ℕ)
    (hk : ∀ᶠ n in hyperfilter ℕ, k n ≤ n) :
    Near (ofSeq (U := hyperfilter ℕ) (fun n ↦ f (meshTime n (k n))))
      (ofSeq (fun n ↦ f (meshTime n (k n + 1)))) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hk, Nat.hyperfilter_le_atTop (eventually_ge_atTop N)] with n hkn hn
  have hl := meshTime_mem n (k n) (hkn.trans (Nat.le_succ n))
  have hr := meshTime_mem n (k n + 1) (Nat.add_le_add_right hkn 1)
  apply hd _ hl _ hr
  rw [meshTime_dist_step]
  exact (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hn 1)).trans_lt hN

end Reeken.NSA
