import Reeken.Nonstandard.Regions

/-! # Standard parts of points appreciably far from an internal boundary -/

open Filter Metric Set

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An internal point on one side, appreciably far from the boundary, has its standard part
deeply on the same side. This allows Section 3's constructed point to be nonstandard. -/
theorem standard_part_mem_deep {u v b : ℕ → Set E} {x : ℕ → E} {a : E} {δ : ℝ}
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (b i)ᶜ)
    (hx : ∀ᶠ i in hyperfilter ℕ, x i ∈ u i)
    (hδ : 0 < δ) (hd : ∀ᶠ i in hyperfilter ℕ, ∀ y ∈ b i, δ ≤ dist y (x i))
    (ha : Near (ofSeq (U := hyperfilter ℕ) x) (std a)) : a ∈ deep u := by
  have hs : InternalSet.Separates (ofSeq u) (ofSeq v) (ofSeq b) := hsep
  apply hs.standard_part_mem_deep hx hδ ?_ ha
  star_transfer
  exact hd

end Reeken.NSA
