import Reeken.Nonstandard.RingContainment

/-! # Paths in the standard inside

Lemma 3 puts any two standard inside points in one finite polygon whose closed
inside misses the original curve. Its connected inside belongs to the standard
inside, so a finite polygonal path there gives the required standard path.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem isPathConnected_standardInside : IsPathConnected (standardInside p) := by
  obtain ⟨q, hq, _, hall⟩ := exists_internal_inner_polygon p hmax hs
  refine isPathConnected_iff.mpr ⟨standardInside_nonempty p hmax hs, ?_⟩
  intro A hA B hB
  obtain ⟨i, hi, hAi, hBi⟩ := (hq.and
    ((eventually_mem_of_mem_deep (hall hA)).and
      (eventually_mem_of_mem_deep (hall hB)))).exists
  have hsep := (q i).2.isSeparating_carrier
  have hsub : inside (q i).2.carrier ⊆ standardInside p := by
    apply hsep.isConnected_inside.isPreconnected.subset_left_of_subset_union
      (isOpen_standardInside p) (isOpen_standardOutside p) (disjoint_standardRegions p)
    · rw [standardRegions_union p hmax hs]
      exact subset_closure.trans hi.2.2
    · exact ⟨A, hAi, hA⟩
  exact ((hsep.isOpen_inside.isConnected_iff_isPathConnected.mp hsep.isConnected_inside).joinedIn
    A hAi B hBi).mono hsub

end Reeken.NSA
