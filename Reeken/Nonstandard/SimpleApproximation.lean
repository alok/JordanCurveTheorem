import Reeken.Geometry.SimplePolygon
import Reeken.Nonstandard.InitialPolygon

/-! # Lemma 2: a simple infinitesimal inscribed polygon

Apply finite minimization at every index. The explicit shortcut reductions rule out
nonadjacent crossings. Lemma 1(i) gives unlimited vertex count, so eventually there
are at least four vertices and the adjacent-overlap argument also applies.
-/

open Filter
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

/-- Loop cutting preserves the infinitesimal edge bound and all admissibility conditions. -/
theorem exists_simple_replacement (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) :
    ∃ q : ℕ → InscribedPolygon f,
      (∀ i, (q i).maxEdge ≤ (p i).maxEdge) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (q i).maxEdge < ε) ∧
      (∀ᶠ i in hyperfilter ℕ, (q i).Simple) ∧
      shadow (fun i ↦ (q i).trace) = f '' Set.Icc 0 1 := by
  classical
  choose q hq hmin using fun i ↦ (p i).exists_minimal
  have hmaxq : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (q i).maxEdge < ε := by
    intro ε hε
    exact (hmax ε hε).mono fun i hi ↦ (hq i).trans_lt hi
  refine ⟨q, hq, hmaxq, ?_, shadow_polygon q hmaxq⟩
  filter_upwards [vertex_count_unlimited q hmaxq 3] with i hi
  exact (hmin i).simple (by omega)

/-- Every simple continuous loop admits an internal simple polygon satisfying
conditions (†), (‡), with infinitesimal edges and precisely the loop as its shadow. -/
theorem exists_simple_polygon (f : SimpleLoop E) :
    ∃ p : ℕ → InscribedPolygon f,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) ∧
      (∀ᶠ i in hyperfilter ℕ, (p i).Simple) ∧
      shadow (fun i ↦ (p i).trace) = f '' Set.Icc 0 1 := by
  obtain ⟨p, hp, _⟩ := exists_initial_polygon f
  obtain ⟨q, _, hq, hs, hshadow⟩ := exists_simple_replacement p hp
  exact ⟨q, hq, hs, hshadow⟩

end Reeken.NSA
