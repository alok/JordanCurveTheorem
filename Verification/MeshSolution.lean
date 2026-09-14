import Reeken.Nonstandard.MeshApproximation

open Filter Set

namespace Verification

universe u

theorem inscribed_mesh_shadow {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 1)) (a : E) :
    (∃ x : ℕ → E,
      (∀ᶠ n in hyperfilter ℕ, x n ∈ ⋃ k : Fin (n + 1),
        segment ℝ (f ((k : ℕ) / (n + 1 : ℝ))) (f (((k : ℕ) + 1) / (n + 1 : ℝ)))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in hyperfilter ℕ, dist (x n) a < ε) ↔
      a ∈ f '' Icc 0 1 := by
  rw [← Reeken.NSA.shadow_meshTrace hf]
  constructor
  · rintro ⟨x, hx, ha⟩
    refine ⟨Reeken.NSA.ofSeq x, ?_, ha⟩
    simpa only [Reeken.NSA.mem_internalSet_ofSeq, Reeken.Geometry.meshTrace,
      Reeken.Geometry.meshTime, Nat.cast_add, Nat.cast_one] using hx
  · rintro ⟨x, hx, ha⟩
    obtain ⟨x, rfl⟩ := Reeken.NSA.ofSeq_surjective x
    refine ⟨x, ?_, ha⟩
    simpa only [Reeken.NSA.mem_internalSet_ofSeq, Reeken.Geometry.meshTrace,
      Reeken.Geometry.meshTime, Nat.cast_add, Nat.cast_one] using hx

end Verification
