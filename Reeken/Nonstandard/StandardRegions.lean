import Reeken.Geometry.PolygonSeparation
import Reeken.Nonstandard.SimpleApproximation
import Reeken.Nonstandard.Regions

/-! # Reeken's standard interior and exterior regions

The finite polygonal separation theorem is applied to the actual simple approximation.
The standard regions are the points appreciably separated from the opposite internal side.
Their common-boundary property and the interior's nonemptiness are proved by the
Section 3 construction in `CommonBoundary.lean`.
-/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Schoenflies.Plane} (p : ℕ → InscribedPolygon f)

def standardInside : Set Schoenflies.Plane := deep (fun i ↦ Schoenflies.inside (p i).trace)

def standardOutside : Set Schoenflies.Plane := deep (fun i ↦ Schoenflies.outside (p i).trace)

theorem eventually_polygon_separates
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple) :
    ∀ᶠ i in hyperfilter ℕ, Schoenflies.IsSeparating (p i).trace := by
  filter_upwards [hs, vertex_count_unlimited p hmax 2] with i hi hn
  exact hi.isSeparating (by omega)

theorem isOpen_standardInside : IsOpen (standardInside p) := isOpen_deep _

theorem isOpen_standardOutside : IsOpen (standardOutside p) := isOpen_deep _

theorem disjoint_standardRegions : Disjoint (standardInside p) (standardOutside p) :=
  disjoint_deep (Eventually.of_forall fun _ ↦ Schoenflies.disjoint_inside_outside)

/-- Section 2's separation transfer, now instantiated with the proved finite polygon theorem. -/
theorem standardRegions_union
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple) :
    standardInside p ∪ standardOutside p = (f '' Icc 0 1)ᶜ := by
  rw [← shadow_polygon p hmax]
  apply deep_union_of_separation
  filter_upwards [eventually_polygon_separates p hmax hs] with i hi
  exact ⟨hi.isOpen_inside, hi.isOpen_outside, Schoenflies.disjoint_inside_outside,
    Schoenflies.inside_union_outside _⟩

/-- Any connected standard set meeting both sides must meet the curve. -/
theorem connected_set_meets_curve
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)
    {s : Set Schoenflies.Plane} (hc : IsPreconnected s)
    (hi : (s ∩ standardInside p).Nonempty) (ho : (s ∩ standardOutside p).Nonempty) :
    (s ∩ f '' Icc 0 1).Nonempty := by
  by_contra h
  have hsub : s ⊆ standardInside p ∪ standardOutside p := by
    rw [standardRegions_union p hmax hs]
    intro x hx hxc
    exact h ⟨x, hx, hxc⟩
  have hleft := hc.subset_left_of_subset_union (isOpen_standardInside p)
    (isOpen_standardOutside p) (disjoint_standardRegions p) hsub hi
  obtain ⟨x, hxs, hxo⟩ := ho
  exact Set.disjoint_left.mp (disjoint_standardRegions p) (hleft hxs) hxo

end Reeken.NSA
