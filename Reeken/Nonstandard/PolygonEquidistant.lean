import Reeken.Nonstandard.ArcShadow
import Reeken.Nonstandard.Equidistant

/-! # Section 3's equal-distance bound for the actual approximating polygon -/

open Filter Set Metric
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

/-- On a compact set away from the limiting cut vertices, every point equidistant from
the two long arcs is appreciably far from the entire approximating polygon. -/
theorem polygon_equidistant_uniform_bound (p : ℕ → InscribedPolygon f)
    (a b : (i : ℕ) → Fin ((p i).n + 1))
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i) {A B : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B))
    {K : Set E} (hK : IsCompact K) (hdis : Disjoint K {f A, f B}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ K,
      infDist x ((p i).forwardArc (a i) (b i)) =
        infDist x ((p i).backwardArc (a i) (b i)) →
      ∀ y ∈ (p i).trace, δ ≤ dist y x := by
  have hdis' := hdis.mono_right (common_arc_shadow_subset p a b hmax hab ha hb)
  obtain ⟨δ, hδ, hd⟩ := equidistant_uniform_bound hK hdis'
    (Eventually.of_forall fun i ↦ ⟨(p i).isCompact_forwardArc (a i) (b i),
      (p i).forwardArc_nonempty (a i) (b i), (p i).isCompact_backwardArc (a i) (b i),
      (p i).backwardArc_nonempty (a i) (b i)⟩)
  refine ⟨δ, hδ, hd.mono fun i hi x hx he ↦ ?_⟩
  simpa only [(p i).arcs_union] using hi x hx he

end Reeken.NSA
