import Reeken.Nonstandard.Loop
import Reeken.Geometry.InscribedPolygon

/-!
# Parameter regularity of an infinitesimal inscribed polygon

Kanovei–Reeken Lemma 1(i): a uniformly infinitesimal edge bound forces uniformly
infinitesimal parameter gaps, unlimited vertex count, and endpoints near zero and one.
All arguments work over an arbitrary ultrafilter.
-/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [NormedAddCommGroup E]
variable {f : SimpleLoop E} (p : ι → InscribedPolygon f)

/-- Even a varying, internally chosen edge has an infinitesimal parameter gap. -/
theorem selected_gap_small
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε)
    (j : (i : ι) → Fin ((p i).n + 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).gap (j i) < ε := by
  have hedge : Near (ofSeq (U := U) (fun i ↦ (p i).vertex (j i)))
      (ofSeq (fun i ↦ (p i).vertex (nextIndex (p i).n (j i)))) := by
    intro ε hε
    exact (hmax ε hε).mono fun i hi ↦ ((p i).edgeLength_le_maxEdge (j i)).trans_lt hi
  by_cases hlast : ∀ᶠ i in U, j i = Fin.last (p i).n
  · have hwrap : Near (ofSeq (U := U) (fun i ↦ f ((p i).time 0)))
        (ofSeq (fun i ↦ f ((p i).time (Fin.last (p i).n)))) := by
      intro ε hε
      filter_upwards [hlast, hedge ε hε] with i hji hi
      change dist ((p i).vertex (j i)) ((p i).vertex (nextIndex (p i).n (j i))) < ε at hi
      simpa only [hji, nextIndex_last, InscribedPolygon.vertex, dist_comm] using hi
    have hg := small_wrap_gap f (fun i ↦ (p i).time 0)
      (fun i ↦ (p i).time (Fin.last (p i).n))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem 0))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem _))
      (Eventually.of_forall fun i ↦ (p i).span_half) hwrap
    intro ε hε
    filter_upwards [hlast, hg ε hε] with i hji hi
    simpa only [hji, InscribedPolygon.gap_last] using hi
  · have hnot := Ultrafilter.eventually_not.mpr hlast
    have hordered : ∀ᶠ i in U,
        (p i).time (j i) ≤ (p i).time (nextIndex (p i).n (j i)) ∧
        (p i).time (nextIndex (p i).n (j i)) - (p i).time (j i) ≤ 1 / 2 := by
      filter_upwards [hnot] with i hi
      obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hi
      have hm : (p i).time k.castSucc ≤ (p i).time k.succ :=
        (p i).increasing.monotone (Fin.castSucc_le_succ k)
      simpa only [← hk, nextIndex_castSucc] using And.intro hm ((p i).forward_half k)
    have hg := small_forward_gap f (fun i ↦ (p i).time (j i))
      (fun i ↦ (p i).time (nextIndex (p i).n (j i)))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem _))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem _)) hordered hedge
    intro ε hε
    filter_upwards [hnot, hg ε hε] with i hi hgi
    obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hi
    simpa only [← hk, nextIndex_castSucc, InscribedPolygon.gap_castSucc] using hgi

/-- Hyperfinite maximization makes the parameter-gap estimate uniform over all edges. -/
theorem maxGap_small
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxGap < ε := by
  classical
  have hex (i : ι) : ∃ j : Fin ((p i).n + 1),
      (p i).maxGap = (p i).gap j := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (p i).gap
    exact ⟨j, hj⟩
  choose j hj using hex
  intro ε hε
  exact (selected_gap_small p hmax j ε hε).mono fun i hi ↦ by rwa [hj i]

/-- No standard finite bound can contain the vertex count of an infinitesimal approximation. -/
theorem vertex_count_unlimited
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε) (N : ℕ) :
    ∀ᶠ i in U, N < (p i).n + 1 := by
  have hg := maxGap_small p hmax (1 / (N + 1 : ℝ)) (by positivity)
  filter_upwards [hg] with i hi
  by_contra hn
  have hle : ((p i).n + 1 : ℝ) ≤ N + 1 := by
    exact_mod_cast (Nat.le_of_not_gt hn).trans (Nat.le_succ N)
  have hpos : 0 ≤ (p i).maxGap := ((p i).gap_pos 0).le.trans ((p i).gap_le_maxGap 0)
  have hprod := mul_le_mul_of_nonneg_right hle hpos
  have hone := (p i).one_le_count_mul_maxGap
  rw [lt_div_iff₀ (by positivity)] at hi
  nlinarith

/-- The first and last parameters approach the two identified endpoints of the interval. -/
theorem first_last_near_endpoints
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε) :
    Near (ofSeq (U := U) (fun i ↦ (p i).time 0)) (std 0) ∧
      Near (ofSeq (U := U) (fun i ↦ (p i).time (Fin.last (p i).n))) (std 1) := by
  have hg := maxGap_small p hmax
  constructor
  · intro ε hε
    filter_upwards [hg ε hε] with i hi
    have hclose := ((p i).gap_le_maxGap (Fin.last (p i).n)).trans_lt hi
    rw [InscribedPolygon.gap_last] at hclose
    change dist ((p i).time 0) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ((p i).time_mem 0).1]
    linarith [((p i).time_mem (Fin.last (p i).n)).2]
  · intro ε hε
    filter_upwards [hg ε hε] with i hi
    have hclose := ((p i).gap_le_maxGap (Fin.last (p i).n)).trans_lt hi
    rw [InscribedPolygon.gap_last] at hclose
    change dist ((p i).time (Fin.last (p i).n)) 1 < ε
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((p i).time_mem _).2.le)]
    linarith [((p i).time_mem 0).1]

end Reeken.NSA
