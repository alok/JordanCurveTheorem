import Reeken.Nonstandard.Regions

/-! # Compact standard sets lie uniformly inside a deep region

This is the compactness step needed to put an entire standard loop into the
internal inner polygon, before transferring its contraction.
-/

open Filter Set

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E]

/-- The internal extension of the whole compact set is included, including nonstandard points. -/
theorem starSet_subset_internalSet_of_compact_subset_deep {K : Set E} (hK : IsCompact K)
    {s : ℕ → Set E} (hsub : K ⊆ deep s) :
    starSet (U := hyperfilter ℕ) K ⊆ internalSet s :=
  InternalSet.starSet_subset_of_isCompact hK hsub

/-- Transfer exposes finite representatives only when the geometric construction needs them. -/
theorem eventually_subset_of_compact_subset_deep {K : Set E} (hK : IsCompact K)
    {s : ℕ → Set E} (hsub : K ⊆ deep s) :
    ∀ᶠ i in hyperfilter ℕ, K ⊆ s i :=
  (internalSet_subset _ _).mp (starSet_subset_internalSet_of_compact_subset_deep hK hsub)

end Reeken.NSA
