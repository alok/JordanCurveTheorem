import Reeken.Geometry.SmallerRadius
import Reeken.Nonstandard.Monads

/-! # A uniform internal choice of the infinitesimal arc -/

open Filter Set Metric Reeken.Geometry

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [MetricSpace E] [Nonempty E]

theorem smallerRadiusSet_inMonad {a : ι → E} {s t : ι → Set E}
    (h : InMonad (internalSet (U := U) s) (ofSeq a) ∨
      InMonad (internalSet (U := U) t) (ofSeq a)) :
    InMonad (internalSet (U := U) (fun i ↦ smallerRadiusSet (a i) (s i) (t i))) (ofSeq a) := by
  rw [inMonad_internalSet_iff]
  intro ε hε
  rcases h with h | h
  · exact ((inMonad_internalSet_iff s a).mp h ε hε).mono fun i hi ↦
      fun _ hx ↦ smallerRadiusSet_subset_ball_of_left (fun _ hy ↦ hi _ hy) hx
  · exact ((inMonad_internalSet_iff t a).mp h ε hε).mono fun i hi ↦
      fun _ hx ↦ smallerRadiusSet_subset_ball_of_right (fun _ hy ↦ hi _ hy) hx

end Reeken.NSA
