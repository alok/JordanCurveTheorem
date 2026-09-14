import Reeken.Geometry.PolygonSeparation

/-! # Filling a closed polygonal loop stays in the enclosing region

If a region has connected unbounded complement, all bounded complementary
components of any subset of the region remain in the region. This is the
geometric containment used when filling a polygonal loop. It is not by itself
a path-homotopy construction.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem inside_subset_of_preconnected_unbounded_compl {U S : Set Plane}
    (hconn : IsPreconnected Uᶜ) (hunbounded : ¬ Bornology.IsBounded Uᶜ) (hSU : S ⊆ U) :
    inside S ⊆ U := by
  intro x hx
  by_contra hxU
  have hsub : Uᶜ ⊆ Sᶜ := compl_subset_compl.mpr hSU
  exact hunbounded (hx.2.subset (hconn.subset_connectedComponentIn hxU hsub))

theorem closure_outside_eq_compl_inside {C : Set Plane} (hC : IsSeparating C) :
    closure (outside C) = (inside C)ᶜ := by
  have hfr := hC.frontier_outside
  rw [hC.isOpen_outside.frontier_eq] at hfr
  ext x
  constructor
  · intro hx hin
    by_cases hout : x ∈ outside C
    · exact Set.disjoint_left.mp disjoint_inside_outside hin hout
    · exact hin.1 (hfr ▸ ⟨hx, hout⟩)
  · intro hx
    by_cases hxc : x ∈ C
    · exact frontier_subset_closure (hC.frontier_outside.symm ▸ hxc)
    · have hr : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hxc
      exact subset_closure (hr.resolve_left hx)

theorem inside_subset_inside_of_carrier_subset {C S : Set Plane}
    (hC : IsSeparating C) (hSC : S ⊆ inside C) : inside S ⊆ inside C := by
  apply inside_subset_of_preconnected_unbounded_compl _ _ hSC
  · rw [← closure_outside_eq_compl_inside hC]
    exact hC.isConnected_outside.isPreconnected.closure
  · rw [← closure_outside_eq_compl_inside hC]
    exact fun hb ↦ hC.not_isBounded_outside (hb.subset subset_closure)

end Reeken.Geometry
