import Reeken.Nonstandard.PolygonRegularity
import Reeken.Nonstandard.Approximation
import Reeken.Nonstandard.InfinitesimalApproximation
import Reeken.Geometry.PolygonApproximation

/-!
# Two-sided infinitesimal approximation for arbitrary admissible polygons

Kanovei–Reeken Lemma 1(ii), without assuming simplicity. It remains valid after any
loop-cutting operation that preserves (†), (‡), and the maximum edge bound.
-/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

theorem polygon_approximates_at_every_scale (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ (p i).trace, ∃ y ∈ f '' Icc 0 1, dist x y < ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ,
      ∀ y ∈ f '' Icc 0 1, ∃ x ∈ (p i).trace, dist x y < ε) := by
  constructor
  · exact fun ε hε ↦ (hmax ε hε).mono fun i hi ↦ (p i).trace_near_curve hi
  · intro ε hε
    have hu := isCompact_Icc.uniformContinuousOn_of_continuous f.continuousOn
    obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
    exact (maxGap_small p hmax δ hδ).mono fun i hi ↦ (p i).curve_near_trace hd hi

/-- One positive infinitesimal uniformly controls the distance in both directions. -/
theorem polygon_infinitesimal_hausdorff (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) :
    ∃ r : Star (hyperfilter ℕ) ℝ, Near r (std 0) ∧
      Holds (fun i ε ↦ 0 < ε ∧
        (∀ x ∈ (p i).trace, ∃ y ∈ f '' Icc 0 1, dist x y < ε) ∧
        (∀ y ∈ f '' Icc 0 1, ∃ x ∈ (p i).trace, dist x y < ε)) r := by
  obtain ⟨hpq, hqp⟩ := polygon_approximates_at_every_scale p hmax
  exact exists_infinitesimal_hausdorff_bound hpq hqp

theorem shadow_polygon (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) :
    shadow (fun i ↦ (p i).trace) = f '' Icc 0 1 := by
  obtain ⟨hpq, hqp⟩ := polygon_approximates_at_every_scale p hmax
  exact shadow_eq_of_approximation
    (isCompact_Icc.image_of_continuousOn f.continuousOn).isClosed hpq hqp

end Reeken.NSA
