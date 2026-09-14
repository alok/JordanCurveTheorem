import Reeken.Nonstandard.OuterPolygon

/-! # Paths in the standard outside

The outer polygon puts any two standard outside points in one finite polygon's
connected outside whose closure misses the original curve. This region belongs
to the standard outside, giving a path between the prescribed points.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem isPathConnected_standardOutside : IsPathConnected (standardOutside p) := by
  obtain ⟨q, hq, _, hall⟩ := exists_internal_outer_polygon p hmax hs
  refine isPathConnected_iff.mpr ⟨standardOutside_nonempty p, ?_⟩
  intro A hA B hB
  obtain ⟨i, hi, hAi, hBi⟩ := (hq.and
    ((eventually_mem_of_mem_deep (hall hA)).and
      (eventually_mem_of_mem_deep (hall hB)))).exists
  have hsep := (q i).2.isSeparating_carrier
  have hsub : outside (q i).2.carrier ⊆ standardOutside p := by
    apply hsep.isConnected_outside.isPreconnected.subset_left_of_subset_union
      (isOpen_standardOutside p) (isOpen_standardInside p) (disjoint_standardRegions p).symm
    · rw [union_comm, standardRegions_union p hmax hs]
      exact subset_closure.trans hi.2.2
    · exact ⟨A, hAi, hA⟩
  exact ((hsep.isOpen_outside.isConnected_iff_isPathConnected.mp hsep.isConnected_outside).joinedIn
    A hAi B hBi).mono hsub

end Reeken.NSA
