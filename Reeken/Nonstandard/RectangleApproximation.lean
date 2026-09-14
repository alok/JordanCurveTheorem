import Reeken.Geometry.PolygonRectangles
import Reeken.Nonstandard.PolygonApproximation
import Reeken.Nonstandard.CompactDeep

/-! # The rectangle arrangement stays in the monad of the curve

Lemma 3 uses rectangle sides and selected shortest boundary connections. We bound
the larger set consisting of the closed rectangles and every possible such
connection. Thus every finite selection satisfies the same estimate. Every
compact standard set disjoint from the curve eventually avoids this entire set.
-/

open Filter Set Metric
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)

def innerConstructionZone (ε : ℕ → ℝ) (i : ℕ) : Set Plane :=
  (p i).rectangleCover (ε i) ∪ (p i).nearestConnectorCover (ε i)

variable (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)

include hmax

theorem rectangle_error_small {ε : ℕ → ℝ}
    (hε : Near (ofSeq (U := hyperfilter ℕ) ε) (std 0)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge + 4 * ε i < η := by
  filter_upwards [hmax (η / 2) (by positivity), hε (η / 8) (by positivity)] with i hi hεi
  have hεi' : |ε i| < η / 8 := by simpa only [Real.dist_eq, sub_zero] using hεi
  have hεbound := (abs_lt.mp hεi').2
  linarith

theorem shadow_innerConstructionZone_subset {ε : ℕ → ℝ}
    (hε : Near (ofSeq (U := hyperfilter ℕ) ε) (std 0)) :
    shadow (innerConstructionZone p ε) ⊆ f '' Icc 0 1 := by
  rw [← shadow_polygon p hmax]
  apply shadow_subset_of_approximation
  intro η hη
  filter_upwards [vertex_count_unlimited p hmax 1, rectangle_error_small p hmax hε hη] with i hni hi
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hx.elim
    ((p i).rectangleCover_near_trace (by omega))
    ((p i).nearestConnectorCover_near_trace (by omega))
  exact ⟨y, hy, hxy.trans_lt hi⟩

/-- The construction misses an entire standard compact set, uniformly at the internal index. -/
theorem eventually_disjoint_innerConstructionZone {ε : ℕ → ℝ}
    (hε : Near (ofSeq (U := hyperfilter ℕ) ε) (std 0))
    {K : Set Plane} (hK : IsCompact K) (hKC : Disjoint K (f '' Icc 0 1)) :
    ∀ᶠ i in hyperfilter ℕ, Disjoint K (innerConstructionZone p ε i) := by
  have hsub : K ⊆ deep (fun i ↦ (innerConstructionZone p ε i)ᶜ) := by
    intro x hx
    change x ∉ shadow (fun i ↦ ((innerConstructionZone p ε i)ᶜ)ᶜ)
    simp only [compl_compl]
    intro hz
    exact Set.disjoint_left.mp hKC hx (shadow_innerConstructionZone_subset p hmax hε hz)
  exact (eventually_subset_of_compact_subset_deep hK hsub).mono fun _ hi ↦
    Set.disjoint_left.mpr fun x hx hz ↦ hi hx hz

/-- The paper's positive infinitesimal supplies rectangles whose interiors cover the
entire internal extension of the original curve. -/
theorem exists_infinitesimal_rectangle_cover :
    ∃ ε : ℕ → ℝ, Near (ofSeq (U := hyperfilter ℕ) ε) (std 0) ∧
      (∀ᶠ i in hyperfilter ℕ, 0 < ε i ∧ f '' Icc 0 1 ⊆ (p i).openRectangleCover (ε i)) ∧
      shadow (innerConstructionZone p ε) ⊆ f '' Icc 0 1 := by
  obtain ⟨ε, hε, hcover⟩ := polygon_infinitesimal_hausdorff p hmax
  obtain ⟨ε, rfl⟩ := ofSeq_surjective ε
  refine ⟨ε, hε, ?_, shadow_innerConstructionZone_subset p hmax hε⟩
  filter_upwards [hcover, vertex_count_unlimited p hmax 1] with i hi hni
  refine ⟨hi.1, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hi.2.2 x hx
  exact (p i).mem_openRectangleCover_of_near_trace (by omega) hi.1 hy
    (by simpa only [dist_comm] using hxy.le)

end Reeken.NSA
