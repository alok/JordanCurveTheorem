import Reeken.Nonstandard.PolygonApproximation
import Reeken.Nonstandard.Monads
import Reeken.Geometry.PolygonArcs

/-!
# The small-arc assertion at polygon vertices

The two arcs cover the polygon even when it self-intersects. Compact inverse continuity
makes one arc infinitesimally small; the distinct standard shadow points rule out both.
-/

open Filter Set Metric
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}
variable (p : ℕ → InscribedPolygon f) (a b : (i : ℕ) → Fin ((p i).n + 1))

theorem forwardArc_inMonad (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i)
    (hparam : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i)))
      (ofSeq (fun i ↦ (p i).time (b i)))) :
    InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ (p i).forwardArc (a i) (b i)))
      (ofSeq (fun i ↦ (p i).vertex (a i))) := by
  intro x hx
  star_cases x
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous f.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  filter_upwards [hx, hab, hparam δ hδ] with i hxi habi hdi
  apply (p i).forwardArc_subset_ball habi ?_ hxi
  intro j haj hjb
  apply hd _ (Ico_subset_Icc_self ((p i).time_mem j)) _
    (Ico_subset_Icc_self ((p i).time_mem (a i)))
  have haj' := (p i).increasing.monotone haj
  have hjb' := (p i).increasing.monotone hjb
  change dist ((p i).time (a i)) ((p i).time (b i)) < δ at hdi
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (haj'.trans hjb'))] at hdi
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr haj')]
  linarith

theorem backwardArc_inMonad
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std 0))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std 1)) :
    InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ (p i).backwardArc (a i) (b i)))
      (ofSeq (fun i ↦ (p i).vertex (a i))) := by
  have ha0 : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i))) (std (f 0)) := by
    simpa only [map_ofSeq, map_std, InscribedPolygon.vertex] using
      ha.map_compact isCompact_Icc f.continuousOn
        (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem (a i)))
        ((std_mem_starSet (Icc 0 1) 0).mpr ⟨le_rfl, zero_le_one⟩)
  intro x hx
  star_cases x
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous f.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  filter_upwards [hx, ha δ hδ, hb δ hδ, ha0 (ε / 2) (half_pos hε)]
    with i hxi hai hbi hcenter
  apply (p i).backwardArc_subset_ball ?_ hxi
  intro j hj
  have hj0 : dist ((p i).vertex j) (f 0) < ε / 2 := by
    rcases hj with hj | hj
    · apply hd _ (Ico_subset_Icc_self ((p i).time_mem j)) _ ⟨le_rfl, zero_le_one⟩
      change dist ((p i).time (a i)) 0 < δ at hai
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((p i).time_mem (a i)).1] at hai
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((p i).time_mem j).1]
      exact ((p i).increasing.monotone hj).trans_lt hai
    · rw [← f.endpoint]
      apply hd _ (Ico_subset_Icc_self ((p i).time_mem j)) _ ⟨zero_le_one, le_rfl⟩
      change dist ((p i).time (b i)) 1 < δ at hbi
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((p i).time_mem (b i)).2.le)] at hbi
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((p i).time_mem j).2.le)]
      have hjb := (p i).increasing.monotone hj
      linarith
  change dist ((p i).vertex (a i)) (f 0) < ε / 2 at hcenter
  have ht := dist_triangle ((p i).vertex j) (f 0) ((p i).vertex (a i))
  rw [dist_comm (f 0) ((p i).vertex (a i))] at ht
  change dist ((p i).vertex j) ((p i).vertex (a i)) < ε
  linarith

theorem polygon_not_inMonad
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (c : Star (hyperfilter ℕ) E) : ¬ InMonad (internalSet (fun i ↦ (p i).trace)) c := by
  have hs := shadow_polygon p hmax
  have h0 : f 0 ∈ shadow (fun i ↦ (p i).trace) := by
    rw [hs]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hh : f (1 / 2) ∈ shadow (fun i ↦ (p i).trace) := by
    rw [hs]
    exact ⟨1 / 2, by norm_num, rfl⟩
  have hne : f 0 ≠ f (1 / 2) := by
    intro h
    have he := f.injectiveOn (by norm_num) (by norm_num) h
    norm_num at he
  exact not_inMonad_of_distinct_shadow h0 hh hne c

/-- Exactly one of the two arcs between near ordered vertices lies in their monad. -/
theorem exactly_one_vertex_arc_small
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i)
    (hne : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i)))
      (ofSeq (fun i ↦ (p i).vertex (b i)))) :
    let F := InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ (p i).forwardArc (a i) (b i)))
      (ofSeq (fun i ↦ (p i).vertex (a i)))
    let B := InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ (p i).backwardArc (a i) (b i)))
      (ofSeq (fun i ↦ (p i).vertex (a i)))
    (F ∨ B) ∧ ¬ (F ∧ B) := by
  constructor
  · have ht := near_parameters_or_endpoints f
      (x := ofSeq (fun i ↦ (p i).time (a i))) (y := ofSeq (fun i ↦ (p i).time (b i)))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem _))
      (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem _)) hne
    rcases ht with ht | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (forwardArc_inMonad p a b hab ht)
    · exact Or.inr (backwardArc_inMonad p a b ha hb)
    · have hfalse : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), False := by
        filter_upwards [hab, ha (1 / 8) (by norm_num), hb (1 / 8) (by norm_num)]
          with i hi hai hbi
        change dist ((p i).time (a i)) 1 < 1 / 8 at hai
        change dist ((p i).time (b i)) 0 < 1 / 8 at hbi
        rw [Real.dist_eq] at hai hbi
        have ha' := (abs_lt.mp hai).1
        have hb' := (abs_lt.mp hbi).2
        have ho := (p i).increasing.monotone hi
        linarith
      obtain ⟨_, h⟩ := hfalse.exists
      exact h.elim
  · rintro ⟨hF, hB⟩
    apply polygon_not_inMonad p hmax (ofSeq (fun i ↦ (p i).vertex (a i)))
    have he : internalSet (U := hyperfilter ℕ) (fun i ↦ (p i).trace) =
        internalSet (fun i ↦ (p i).forwardArc (a i) (b i)) ∪
        internalSet (fun i ↦ (p i).backwardArc (a i) (b i)) := by
      rw [← internalSet_union]
      congr 1
      funext i
      exact ((p i).arcs_union (a i) (b i)).symm
    rw [he]
    exact hF.union hB

end Reeken.NSA
