import Reeken.Geometry.Segments
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform inscribed polygonal meshes

There are `n + 1` edges, so the denominator never vanishes. For a loop the last
endpoint equals the first one. Simplicity is deliberately not imposed on this initial mesh.
-/

open Set

namespace Reeken.Geometry

/-- The `k`th parameter of a mesh with `n + 1` edges. -/
noncomputable def meshTime (n k : ℕ) : ℝ := k / (n + 1 : ℝ)

theorem meshTime_mem (n k : ℕ) (hk : k ≤ n + 1) : meshTime n k ∈ Icc (0 : ℝ) 1 := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hn.le
  · rw [meshTime, div_le_one hn]
    exact_mod_cast hk

theorem meshTime_step (n k : ℕ) :
    meshTime n (k + 1) - meshTime n k = 1 / (n + 1 : ℝ) := by
  simp only [meshTime, Nat.cast_add, Nat.cast_one]
  ring

theorem meshTime_dist_step (n k : ℕ) :
    dist (meshTime n k) (meshTime n (k + 1)) = 1 / (n + 1 : ℝ) := by
  rw [dist_comm, Real.dist_eq, meshTime_step, abs_of_pos (by positivity)]

/-- Every parameter lies between consecutive mesh parameters, including the endpoint `1`. -/
theorem exists_mesh_interval (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : Fin (n + 1), t ∈ Icc (meshTime n k) (meshTime n (k + 1)) := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  by_cases ht1 : t = 1
  · refine ⟨⟨n, Nat.lt_succ_self n⟩, ?_⟩
    subst t
    constructor
    · exact (meshTime_mem n n (Nat.le_succ n)).2
    · simp [meshTime, ne_of_gt hn]
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    let k : ℕ := ⌊t * (n + 1 : ℝ)⌋₊
    have hnonneg : 0 ≤ t * (n + 1 : ℝ) := mul_nonneg ht.1 hn.le
    have hk : k < n + 1 := by
      apply (Nat.floor_lt hnonneg).mpr
      push_cast
      nlinarith
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · change (k : ℝ) / (n + 1 : ℝ) ≤ t
      exact (div_le_iff₀ hn).mpr (Nat.floor_le hnonneg)
    · change t ≤ ((k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)
      rw [le_div_iff₀ hn, Nat.cast_add, Nat.cast_one]
      exact (Nat.lt_floor_add_one _).le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The union of the segments between consecutive sampled values. -/
def meshTrace (f : ℝ → E) (n : ℕ) : Set E :=
  ⋃ k : Fin (n + 1), segment ℝ (f (meshTime n k)) (f (meshTime n (k + 1)))

theorem left_mem_meshTrace (f : ℝ → E) (n : ℕ) (k : Fin (n + 1)) :
    f (meshTime n k) ∈ meshTrace f n :=
  mem_iUnion.mpr ⟨k, left_mem_segment ℝ _ _⟩

theorem meshTrace_nonempty (f : ℝ → E) (n : ℕ) : (meshTrace f n).Nonempty :=
  ⟨f (meshTime n 0), left_mem_meshTrace f n ⟨0, Nat.zero_lt_succ _⟩⟩

/-- Every sufficiently fine inscribed mesh approximates the entire parametrized curve
in both directions. The estimate is uniform over all segments and all curve points. -/
theorem meshTrace_approximates {f : ℝ → E} (hf : UniformContinuousOn f (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
      (∀ x ∈ meshTrace f n, ∃ y ∈ f '' Icc 0 1, dist x y < ε) ∧
      (∀ y ∈ f '' Icc 0 1, ∃ x ∈ meshTrace f n, dist x y < ε) := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hf ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hstep : 1 / (n + 1 : ℝ) < δ :=
    (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans_lt hN
  constructor
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hleft := meshTime_mem n k (Nat.le_of_lt k.isLt)
    have hright := meshTime_mem n (k + 1) (Nat.succ_le_of_lt k.isLt)
    refine ⟨f (meshTime n k), ⟨meshTime n k, hleft, rfl⟩, ?_⟩
    have hedge := hd _ hleft _ hright (by simpa only [meshTime_dist_step] using hstep)
    rw [dist_comm]
    exact (dist_left_le_of_mem_segment hk).trans_lt hedge
  · rintro y ⟨t, ht, rfl⟩
    obtain ⟨k, hk⟩ := exists_mesh_interval n ht
    have hleft := meshTime_mem n k (Nat.le_of_lt k.isLt)
    refine ⟨f (meshTime n k), left_mem_meshTrace f n k, hd _ hleft _ ht ?_⟩
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hk.1)]
    calc
      t - meshTime n k ≤ meshTime n (k + 1) - meshTime n k := sub_le_sub_right hk.2 _
      _ = 1 / (n + 1 : ℝ) := meshTime_step n k
      _ < δ := hstep

end Reeken.Geometry
