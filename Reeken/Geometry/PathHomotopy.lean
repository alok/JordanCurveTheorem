import Reeken.Geometry.Segments
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Thickening

/-! # Straight homotopies for finite polygonal loop contractions

Pointwise segment containment gives a homotopy with fixed endpoints. A compact
path in an open set therefore remains homotopic, inside that set, to every
sufficiently close path with the same endpoints. This supplies the deformation
step when replacing continuous paths by finite polygonal paths.
-/

open Set unitInterval

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}

noncomputable def linearPathHomotopy (p q : Path a b) : p.Homotopy q where
  toFun z := (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2
  continuous_toFun := by fun_prop
  map_zero_left := by intro t; simp
  map_one_left := by intro t; simp
  prop' := by
    intro t s hs
    rcases hs with rfl | hs
    · simp
      module
    · have he : s = 1 := mem_singleton_iff.mp hs
      subst s
      simp
      module

theorem linearPathHomotopy_mem_segment (p q : Path a b) (z : I × I) :
    linearPathHomotopy p q z ∈ segment ℝ (p z.2) (q z.2) := by
  exact ⟨1 - (z.1 : ℝ), (z.1 : ℝ), sub_nonneg.mpr z.1.2.2, z.1.2.1,
    sub_add_cancel _ _, rfl⟩

theorem exists_homotopy_of_segments_subset {p q : Path a b} {U : Set E}
    (h : ∀ t, segment ℝ (p t) (q t) ⊆ U) :
    ∃ H : p.Homotopy q, ∀ z, H z ∈ U :=
  ⟨linearPathHomotopy p q, fun z ↦ h z.2 (linearPathHomotopy_mem_segment p q z)⟩

theorem exists_homotopy_of_uniformly_close {U : Set E} (hU : IsOpen U)
    (p : Path a b) (hp : ∀ t, p t ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Path a b, (∀ t, dist (q t) (p t) < δ) →
      ∃ H : p.Homotopy q, ∀ z, H z ∈ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_range p.continuous).exists_thickening_subset_open
    hU (range_subset_iff.mpr hp)
  refine ⟨δ, hδ, fun q hq ↦ exists_homotopy_of_segments_subset fun t x hx ↦ ?_⟩
  apply hsub
  apply Metric.mem_thickening_iff.mpr
  refine ⟨p t, mem_range_self t, ?_⟩
  exact (convex_ball (p t) δ).segment_subset (by simpa using hδ) (hq t) hx

end Reeken.Geometry
