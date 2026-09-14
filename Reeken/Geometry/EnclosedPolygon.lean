import Reeken.Geometry.EnclosedSets

/-! # A polygon cut from a closed inside stays on the inside

A closed curve contained in another separating curve's closed inside has its
open inside in the original open inside. Connectedness and unboundedness of the
original exterior give the containment, including at shared boundary arcs.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem outside_eq_compl_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    outside C = (closure (inside C))ᶜ := by
  rw [(IsRegionOf.inside C).closure_eq hC]
  ext x
  change (x ∉ C ∧ ¬ Bornology.IsBounded (connectedComponentIn Cᶜ x)) ↔
    ¬ ((x ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ x)) ∨ x ∈ C)
  tauto

theorem inside_subset_inside_of_carrier_subset_closed_inside {C S : Set Plane}
    (hC : IsSeparating C) (hS : IsClosed S) (hSC : S ⊆ closure (inside C)) :
    inside S ⊆ inside C := by
  have hsub : inside S ⊆ closure (inside C) := by
    apply inside_subset_of_preconnected_unbounded_compl _ _ hSC
    · rw [← outside_eq_compl_closure_inside hC]
      exact hC.isConnected_outside.isPreconnected
    · rw [← outside_eq_compl_closure_inside hC]
      exact hC.not_isBounded_outside
  have hd : Disjoint (inside S) (outside C) := by
    rw [outside_eq_compl_closure_inside hC]
    exact disjoint_left.mpr fun _ hx hy ↦ hy (hsub hx)
  have hdc := hd.closure_right (Schoenflies.isOpen_inside hS)
  rw [closure_outside_eq_compl_inside hC] at hdc
  intro x hx
  by_contra hn
  exact disjoint_left.mp hdc hx hn

end Reeken.Geometry
