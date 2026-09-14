import Reeken.Nonstandard.EdgePoints
import Reeken.Geometry.PointArcs

/-! # Lemma 1(iii): cuts at arbitrary points of polygon edges -/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

/-- Exactly one arc between near points of an infinitesimal inscribed polygon
lies in their monad. Edge indices are in cyclic order; on the same edge the
forward cut is the segment between the points. -/
theorem exactly_one_point_arc_small
    (p : ℕ → InscribedPolygon f)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (a b : (i : ℕ) → Fin ((p i).n + 1)) (x y : ℕ → E)
    (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i)
    (hx : ∀ᶠ i in hyperfilter ℕ, x i ∈ (p i).edge (a i))
    (hy : ∀ᶠ i in hyperfilter ℕ, y i ∈ (p i).edge (b i))
    (hxy : Near (ofSeq (U := hyperfilter ℕ) x) (ofSeq y)) :
    let F := InMonad (internalSet (U := hyperfilter ℕ)
      (fun i ↦ (p i).forwardPointArc (a i) (b i) (x i) (y i))) (ofSeq x)
    let B := InMonad (internalSet (U := hyperfilter ℕ)
      (fun i ↦ (p i).backwardPointArc (a i) (b i) (x i) (y i))) (ofSeq x)
    (F ∨ B) ∧ ¬ (F ∧ B) := by
  have hxa := edge_point_near_vertex p hmax a x hx
  have hyb := edge_point_near_vertex p hmax b y hy
  have hEA := (edge_inMonad p hmax a).change_center hxa.symm
  have hEB := (edge_inMonad p hmax b).change_center (hyb.symm.trans hxy.symm)
  constructor
  · by_cases heq : ∀ᶠ i in hyperfilter ℕ, a i = b i
    · left
      apply hEA.mono
      apply (internalSet_subset _ _).mpr
      filter_upwards [heq, hx, hy] with i hi hxi hyi
      rw [InscribedPolygon.forwardPointArc, if_pos hi]
      rw [← hi] at hyi
      exact (convex_segment _ _).segment_subset hxi hyi
    · have hlt : ∀ᶠ i in hyperfilter ℕ, a i < b i := by
        filter_upwards [hab, (Ultrafilter.eventually_not.mpr heq)] with i hi hni
        exact lt_of_le_of_ne hi hni
      have hne := near_incident_vertices p hmax a b x y hx hy hxy
      rcases (exactly_one_vertex_arc_small p a b hmax hab hne).1 with hF | hB
      · left
        have hs := (hF.change_center hxa.symm).union hEB
        rw [← internalSet_union] at hs
        apply hs.mono
        apply (internalSet_subset _ _).mpr
        filter_upwards [hlt, hx, hy] with i hi hxi hyi
        exact (p i).forwardPointArc_subset hi hxi hyi
      · right
        have hs := (hB.change_center hxa.symm).union hEA
        rw [← internalSet_union] at hs
        apply hs.mono
        apply (internalSet_subset _ _).mpr
        filter_upwards [hx, hy] with i hxi hyi
        exact (p i).backwardPointArc_subset hxi hyi
  · rintro ⟨hF, hB⟩
    apply polygon_not_inMonad p hmax (ofSeq x)
    have hs := ((hF.union hB).union hEA).union hEB
    rw [← internalSet_union, ← internalSet_union, ← internalSet_union] at hs
    apply hs.mono
    apply (internalSet_subset _ _).mpr
    exact Eventually.of_forall fun i ↦ (p i).trace_subset_pointArcs_edges (x i) (y i)

end Reeken.NSA
