import Reeken.Geometry.SmallEnclosures
import Reeken.Nonstandard.Monads

/-! # The inside of an infinitesimal barrier is infinitesimal

This is the enclosure estimate used after Lemma 1(iii) makes one arc of a
crosscut barrier infinitesimal. No Jordan theorem is required for this estimate.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {ι : Type*} {U : Ultrafilter ι}

theorem InMonad.inside {C : ι → Set Plane} {a : ι → Plane}
    (h : InMonad (internalSet (U := U) C) (ofSeq a)) :
    InMonad (internalSet (U := U) (fun i ↦ inside (C i))) (ofSeq a) := by
  rw [inMonad_internalSet_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / 4) (by positivity)] with i hi
  intro x hx
  have hdist := dist_le_of_mem_inside_of_boundary_dist_le (fun y hy ↦ (hi y hy).le) hx
  have hsqrt : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hbound : Real.sqrt 2 * (ε / 4) ≤ 2 * (ε / 4) :=
    mul_le_mul_of_nonneg_right hsqrt (by positivity)
  linarith

/-- A standard point enclosed by an infinitesimal barrier lies in its monad. -/
theorem near_std_of_mem_inside_small_barrier {C : ι → Set Plane} {a : ι → Plane}
    (h : InMonad (internalSet (U := U) C) (ofSeq a)) {x : Plane}
    (hx : ∀ᶠ i in U, x ∈ inside (C i)) : Near (ofSeq (U := U) a) (std x) :=
  (h.inside (std x) hx).symm

end Reeken.NSA
