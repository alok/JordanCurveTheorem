import Reeken.Geometry.LoopPuncture
import Schoenflies.Plane

/-! # Two crossings of a closed domain by a simple closed curve

Puncturing a simple closed curve leaves it connected. A connected set that goes
from the interior to the exterior of a closed domain must meet its boundary.
Removing one crossing and applying this again supplies a second, distinct crossing.
-/

open Set Schoenflies

namespace Reeken.Geometry

variable {E : Type*} [TopologicalSpace E]

theorem exists_frontier_crossing {S D : Set E} (hS : IsPreconnected S) (hD : IsClosed D)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) (haD : a ∈ interior D) (hbD : b ∉ D) :
    (S ∩ frontier D).Nonempty := by
  by_contra hnone
  have hsub : S ⊆ interior D ∪ Dᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · apply Or.inl
      by_contra hxi
      exact hnone ⟨x, hx, by rw [hD.frontier_eq]; exact ⟨hxD, hxi⟩⟩
    · exact Or.inr hxD
  have hdis : Disjoint (interior D) Dᶜ := Set.disjoint_left.mpr fun _ hx hy ↦
    hy (interior_subset hx)
  have hleft := hS.subset_left_of_subset_union isOpen_interior hD.isOpen_compl hdis
    hsub ⟨a, ha, haD⟩
  exact hbD (interior_subset (hleft hb))

theorem exists_two_frontier_crossings {C D : Set Plane} (hC : IsJordanCurve C) (hD : IsClosed D)
    {a b : Plane} (ha : a ∈ C) (hb : b ∈ C) (haD : a ∈ interior D) (hbD : b ∉ D) :
    ∃ x ∈ C ∩ frontier D, ∃ y ∈ C ∩ frontier D, x ≠ y := by
  obtain ⟨x, hxC, hxD⟩ := exists_frontier_crossing hC.isConnected.isPreconnected hD ha hb haD hbD
  have hax : a ≠ x := by
    intro h
    subst x
    rw [hD.frontier_eq] at hxD
    exact hxD.2 haD
  have hbx : b ≠ x := by
    intro h
    subst x
    exact hbD (hD.frontier_subset hxD)
  obtain ⟨y, hy, hyD⟩ := exists_frontier_crossing (isPreconnected_punctured_jordan hC x)
    hD ⟨ha, hax⟩ ⟨hb, hbx⟩ haD hbD
  exact ⟨x, ⟨hxC, hxD⟩, y, ⟨hy.1, hyD⟩, Ne.symm hy.2⟩

end Reeken.Geometry
