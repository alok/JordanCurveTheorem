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
  have hb : a ∉ shadow b := by
    refine (not_mem_shadow_iff b a).mpr ⟨δ / 2, half_pos hδ, ?_⟩
    filter_upwards [hd, ha (δ / 2) (half_pos hδ)] with i hi hai y hy
    have h := hi y hy
    have ht := dist_triangle y a (x i)
    have hai' : dist a (x i) < δ / 2 := by simpa only [dist_comm] using hai
    linarith
  have hai : ∀ᶠ i in hyperfilter ℕ, a ∈ u i := by
    filter_upwards [hsep, hx, hd, ha δ hδ] with i hi hxi hdi hnear
    apply ball_subset_side hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hδ hxi hdi
    change dist a (x i) < δ
    simpa only [dist_comm] using hnear
  exact mem_deep_of_separation hsep hai hb

end Reeken.NSA
