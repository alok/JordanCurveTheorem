import Reeken.Geometry.UniformMesh
import Reeken.Geometry.PathHomotopy
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # A continuous parametrization of a finite polygonal mesh

Choose a containing mesh interval at each parameter. The affine formulas agree
at shared endpoints, so finite closed pasting proves continuity independently
of the choices. This permits polygonal approximation of arbitrary continuous
loops, without a simplicity assumption on the loop.
-/

open Set unitInterval

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem meshTime_le_iff (n j k : ℕ) : meshTime n j ≤ meshTime n k ↔ j ≤ k := by
  rw [meshTime, meshTime, div_le_div_iff_of_pos_right (by positivity)]
  exact Nat.cast_le

noncomputable def meshFormula (f : ℝ → E) (n k : ℕ) (t : ℝ) : E :=
  (1 - ((n + 1 : ℝ) * t - k)) • f (meshTime n k) +
    ((n + 1 : ℝ) * t - k) • f (meshTime n (k + 1))

theorem meshFormula_left (f : ℝ → E) (n k : ℕ) :
    meshFormula f n k (meshTime n k) = f (meshTime n k) := by
  have h : (n + 1 : ℝ) * meshTime n k - k = 0 := by
    dsimp [meshTime]
    field_simp
    ring
  simp [meshFormula, h]

theorem meshFormula_right (f : ℝ → E) (n k : ℕ) :
    meshFormula f n k (meshTime n (k + 1)) = f (meshTime n (k + 1)) := by
  have h : (n + 1 : ℝ) * meshTime n (k + 1) - k = 1 := by
    dsimp [meshTime]
    field_simp
    push_cast
    ring
  simp [meshFormula, h]

theorem meshFormula_agree (f : ℝ → E) (n j k : ℕ) {t : ℝ}
    (hj : t ∈ Icc (meshTime n j) (meshTime n (j + 1)))
    (hk : t ∈ Icc (meshTime n k) (meshTime n (k + 1))) :
    meshFormula f n j t = meshFormula f n k t := by
  suffices ∀ j k : ℕ, j ≤ k →
      t ∈ Icc (meshTime n j) (meshTime n (j + 1)) →
      t ∈ Icc (meshTime n k) (meshTime n (k + 1)) →
      meshFormula f n j t = meshFormula f n k t by
    rcases le_total j k with h | h
    · exact this j k h hj hk
    · exact (this k j h hk hj).symm
  intro j k hjk hj hk
  rcases eq_or_lt_of_le hjk with rfl | hjk
  · rfl
  have horder : meshTime n (j + 1) ≤ meshTime n k :=
    (meshTime_le_iff _ _ _).mpr (by omega)
  have htj : t = meshTime n (j + 1) := le_antisymm hj.2 (horder.trans hk.1)
  have htk : t = meshTime n k := le_antisymm (hj.2.trans horder) hk.1
  rw [htj, meshFormula_right, ← htj, htk, meshFormula_left]

noncomputable def meshIndex (n : ℕ) (t : I) : Fin (n + 1) :=
  Classical.choose (exists_mesh_interval n t.2)

theorem meshIndex_mem (n : ℕ) (t : I) :
    (t : ℝ) ∈ Icc (meshTime n (meshIndex n t)) (meshTime n (meshIndex n t + 1)) :=
  Classical.choose_spec (exists_mesh_interval n t.2)

noncomputable def meshInterpolation (f : ℝ → E) (n : ℕ) (t : I) : E :=
  meshFormula f n (meshIndex n t) t

theorem meshInterpolation_eq (f : ℝ → E) (n : ℕ) (k : Fin (n + 1)) {t : I}
    (ht : (t : ℝ) ∈ Icc (meshTime n k) (meshTime n (k + 1))) :
    meshInterpolation f n t = meshFormula f n k t :=
  meshFormula_agree f n _ _ (meshIndex_mem n t) ht

theorem continuous_meshInterpolation (f : ℝ → E) (n : ℕ) :
    Continuous (meshInterpolation f n) := by
  let S : Fin (n + 1) → Set I := fun k ↦
    {t | (t : ℝ) ∈ Icc (meshTime n k) (meshTime n (k + 1))}
  apply (locallyFinite_of_finite S).continuous
  · ext t
    simp only [mem_iUnion, mem_univ, iff_true]
    exact exists_mesh_interval n t.2
  · intro k
    exact isClosed_Icc.preimage continuous_subtype_val
  · intro k
    have h : Continuous (fun t : I ↦ meshFormula f n k (t : ℝ)) := by
      dsimp [meshFormula]
      fun_prop
    exact h.continuousOn.congr fun t ht ↦ meshInterpolation_eq f n k ht

theorem meshInterpolation_zero (f : ℝ → E) (n : ℕ) :
    meshInterpolation f n 0 = f 0 := by
  rw [meshInterpolation_eq f n ⟨0, by omega⟩ (by
    change (0 : ℝ) ∈ Icc (meshTime n 0) (meshTime n 1)
    simp [meshTime, le_of_lt (show (0 : ℝ) < n + 1 by positivity)])]
  have h := meshFormula_left f n 0
  simpa [meshTime] using h

theorem meshInterpolation_one (f : ℝ → E) (n : ℕ) :
    meshInterpolation f n 1 = f 1 := by
  have hlast : meshTime n (n + 1) = 1 := by
    simp [meshTime, ne_of_gt (show (0 : ℝ) < n + 1 by positivity)]
  rw [meshInterpolation_eq f n ⟨n, by omega⟩ (by
    change (1 : ℝ) ∈ Icc (meshTime n n) (meshTime n (n + 1))
    exact ⟨(meshTime_mem n n (by omega)).2, hlast.symm.le⟩)]
  simpa [hlast] using meshFormula_right f n n

theorem meshFormula_mem_segment (f : ℝ → E) (n k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (meshTime n k) (meshTime n (k + 1))) :
    meshFormula f n k t ∈ segment ℝ (f (meshTime n k)) (f (meshTime n (k + 1))) := by
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hlo : (k : ℝ) ≤ (n + 1 : ℝ) * t := by
    have h := (div_le_iff₀ hN).mp ht.1
    linarith
  have hhi : (n + 1 : ℝ) * t ≤ (k : ℝ) + 1 := by
    have h := (le_div_iff₀ hN).mp ht.2
    push_cast at h
    linarith
  exact ⟨1 - ((n + 1 : ℝ) * t - k), (n + 1 : ℝ) * t - k,
    by linarith, by linarith, by ring, rfl⟩

noncomputable def meshPath {a b : E} (p : Path a b) (n : ℕ) : Path a b where
  toFun := meshInterpolation p.extend n
  continuous_toFun := continuous_meshInterpolation _ _
  source' := by rw [meshInterpolation_zero]; simp
  target' := by rw [meshInterpolation_one]; simp

theorem meshPath_mem_trace {a b : E} (p : Path a b) (n : ℕ) (t : I) :
    meshPath p n t ∈ meshTrace p.extend n :=
  mem_iUnion.mpr ⟨meshIndex n t, meshFormula_mem_segment _ _ _ (meshIndex_mem n t)⟩

theorem meshPath_uniformly_close {a b : E} (p : Path a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : I, dist (meshPath p n t) (p t) < ε := by
  have hu : UniformContinuousOn p.extend (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous p.continuous_extend.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn t ↦ ?_⟩
  have hstep : 1 / (n + 1 : ℝ) < δ :=
    (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans_lt hN
  let k := meshIndex n t
  have ht := meshIndex_mem n t
  have hleft : dist (meshTime n k) (t : ℝ) < δ := by
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    calc
      (t : ℝ) - meshTime n k ≤ meshTime n (k + 1) - meshTime n k :=
        sub_le_sub_right ht.2 _
      _ = 1 / (n + 1 : ℝ) := meshTime_step n k
      _ < δ := hstep
  have hright : dist (meshTime n (k + 1)) (t : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    calc
      meshTime n (k + 1) - (t : ℝ) ≤ meshTime n (k + 1) - meshTime n k :=
        sub_le_sub_left ht.1 _
      _ = 1 / (n + 1 : ℝ) := meshTime_step n k
      _ < δ := hstep
  have hL : p.extend (meshTime n k) ∈ Metric.ball (p t) ε := by
    simpa using hd _ (meshTime_mem n k (by omega)) _ t.2 hleft
  have hR : p.extend (meshTime n (k + 1)) ∈ Metric.ball (p t) ε := by
    simpa using hd _ (meshTime_mem n (k + 1) (by omega)) _ t.2 hright
  exact (convex_ball (p t) ε).segment_subset hL hR
    (meshFormula_mem_segment _ _ _ ht)

/-- An arbitrary continuous path in an open set is homotopic there, with fixed
endpoints, to an actual finite polygonal mesh path. No injectivity is assumed. -/
theorem exists_meshPath_homotopy {a b : E} {U : Set E} (hU : IsOpen U)
    (p : Path a b) (hp : ∀ t, p t ∈ U) :
    ∃ n : ℕ, ∃ H : p.Homotopy (meshPath p n), ∀ z, H z ∈ U := by
  obtain ⟨δ, hδ, hclose⟩ := exists_homotopy_of_uniformly_close hU p hp
  obtain ⟨N, hN⟩ := meshPath_uniformly_close p hδ
  obtain ⟨H, hH⟩ := hclose (meshPath p N) (hN N le_rfl)
  exact ⟨N, H, hH⟩

end Reeken.Geometry
