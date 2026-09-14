import Reeken.Nonstandard.CompactSeparation
import Reeken.Nonstandard.Regions

/-! # Compact standard sets lie uniformly inside a deep region

This is the compactness step needed to put an entire standard loop into the
internal inner polygon, before transferring its contraction.
-/

open Filter Set

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E]

/-- Pointwise deep inclusion of a compact standard set transfers to uniform internal inclusion. -/
theorem eventually_subset_of_compact_subset_deep {K : Set E} (hK : IsCompact K)
    {s : ℕ → Set E} (hsub : K ⊆ deep s) :
    ∀ᶠ i in hyperfilter ℕ, K ⊆ s i := by
  have hd : Disjoint K (shadow (fun i ↦ (s i)ᶜ) ∩ shadow (fun i ↦ (s i)ᶜ)) := by
    rw [Set.disjoint_left]
    exact fun x hx hh ↦ hsub hx hh.1
  obtain ⟨δ, hδ, hsep⟩ := compact_separation_from_common_shadow hK hd
  filter_upwards [hsep] with i hi x hx
  by_contra hn
  have h := hi x hx x hn x hn
  simp only [dist_self, max_self, not_le_of_gt hδ] at h

/-- The internal extension of the whole compact set is included, including nonstandard points. -/
theorem starSet_subset_internalSet_of_compact_subset_deep {K : Set E} (hK : IsCompact K)
    {s : ℕ → Set E} (hsub : K ⊆ deep s) :
    starSet (U := hyperfilter ℕ) K ⊆ internalSet s :=
  (internalSet_subset _ _).mpr (eventually_subset_of_compact_subset_deep hK hsub)

end Reeken.NSA
