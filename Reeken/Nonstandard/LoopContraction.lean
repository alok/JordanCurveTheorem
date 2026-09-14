import Reeken.Nonstandard.InsideConnectivity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! # Compact-loop transfer through the inner polygon

This is the reduction of simple connectivity to the finite polygonal foundation.
That foundation is an explicit hypothesis here and remains an open obligation;
this module does not assert unconditional simple connectivity.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

/-- Every compact subset of the standard inside lies in the inside of one actual
finite simple polygon, and that whole polygonal inside belongs to the standard inside. -/
theorem exists_polygon_inside_of_isCompact {K : Set Plane} (hK : IsCompact K)
    (hne : K.Nonempty) (hKU : K ⊆ standardInside p) :
    ∃ m : ℕ, ∃ Q : ClosedPolygon m,
      K ⊆ inside Q.carrier ∧ inside Q.carrier ⊆ standardInside p := by
  obtain ⟨q, hq, _, hall⟩ := exists_internal_inner_polygon p hmax hs
  obtain ⟨i, hi, hKi⟩ := (hq.and
    (eventually_subset_of_compact_subset_deep hK (hKU.trans hall))).exists
  refine ⟨(q i).1, (q i).2, hKi, ?_⟩
  apply (q i).2.isSeparating_carrier.isConnected_inside.isPreconnected.subset_left_of_subset_union
    (isOpen_standardInside p) (isOpen_standardOutside p) (disjoint_standardRegions p)
  · rw [standardRegions_union p hmax hs]
    exact subset_closure.trans hi.2.2
  · obtain ⟨A, hA⟩ := hne
    exact ⟨A, hKi hA, hKU hA⟩

/-- The complete NSA step for arbitrary continuous loops, conditional only on the
still-unproved finite polygonal simple-connectivity theorem. -/
theorem isSimplyConnected_standardInside_of_polygon
    (hfinite : ∀ (m : ℕ) (Q : ClosedPolygon m), IsSimplyConnected (inside Q.carrier)) :
    IsSimplyConnected (standardInside p) := by
  refine isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mpr
    ⟨isPathConnected_standardInside p hmax hs, ?_⟩
  intro x γ hγ
  obtain ⟨m, Q, hsub, hQU⟩ := exists_polygon_inside_of_isCompact p hmax hs
    (isCompact_range γ.continuous) (range_nonempty γ) (range_subset_iff.mpr hγ)
  obtain ⟨H, hH⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp (hfinite m Q)).2
    x γ (fun t ↦ hsub (mem_range_self t))
  exact ⟨H, fun t ↦ hQU (hH t)⟩

end Reeken.NSA
