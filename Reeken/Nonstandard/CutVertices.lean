import Reeken.Nonstandard.PolygonRegularity
import Reeken.Geometry.PolygonApproximation

/-! # Selecting polygon vertices at prescribed standard parameters -/

open Filter Set Topology
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E}

/-- Every standard parameter is infinitesimally close to a selected polygon parameter. -/
theorem exists_cut_vertex (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    {A : ℝ} (hA : A ∈ Icc 0 1) :
    ∃ a : (i : ℕ) → Fin ((p i).n + 1),
      Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A) := by
  classical
  choose a ha using fun i ↦ (p i).exists_near_parameter hA
  refine ⟨a, fun ε hε ↦ ?_⟩
  filter_upwards [maxGap_small p hmax ε hε] with i hi
  rw [dist_comm]
  exact (ha i).trans_lt hi

/-- Distinct ordered standard cut parameters give distinct ordered polygon vertices eventually. -/
theorem exists_ordered_cut_vertices (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    {A B : ℝ} (hA : A ∈ Icc 0 1) (hB : B ∈ Icc 0 1) (hAB : A < B) :
    ∃ a b : (i : ℕ) → Fin ((p i).n + 1),
      Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A) ∧
      Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B) ∧
      ∀ᶠ i in hyperfilter ℕ, a i < b i := by
  obtain ⟨a, ha⟩ := exists_cut_vertex p hmax hA
  obtain ⟨b, hb⟩ := exists_cut_vertex p hmax hB
  refine ⟨a, b, ha, hb, ?_⟩
  have h := ((near_std_iff_tendsto _ _).mp ha).eventually_lt
    ((near_std_iff_tendsto _ _).mp hb) hAB
  exact h.mono fun i hi ↦ (p i).increasing.lt_iff_lt.mp hi

end Reeken.NSA
