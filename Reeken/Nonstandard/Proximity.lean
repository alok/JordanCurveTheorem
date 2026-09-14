import Reeken.Nonstandard.Hypermetric
import Reeken.Nonstandard.Shadow

/-!
# Realizing infinitesimal proximity

For two internal functions on an internal set, arbitrarily close values at every
positive standard scale are realized by one pair of infinitely close values. This
follows from the shadow theorem applied to the internal image of the distance function.
It uses no additional saturation construction and works over any free ultrafilter on ℕ.
-/

open Filter Set

namespace Reeken.NSA.InternalSet

variable {α β : Type*} [Nonempty α] [PseudoMetricSpace β] {U : Ultrafilter ℕ}

/-- A single internal argument realizes proximity at all positive standard scales. -/
theorem exists_near_iff (hU : (U : Filter ℕ) ≤ atTop) (s : InternalSet U α)
    (f g : Star U (α → β)) :
    (∃ x ∈ s, Near (app f x) (app g x)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, starDist (app f x) (app g x) < std ε := by
  constructor
  · rintro ⟨x, hx, hfg⟩ ε hε
    exact ⟨x, hx, (near_iff_starDist _ _).mp hfg ε hε⟩
  · intro h
    let d : Star U (α → ℝ) := Germ.map₂ (fun f g a ↦ dist (f a) (g a)) f g
    have hd (x : Star U α) : app d x = starDist (app f x) (app g x) := by
      dsimp only [d]
      star_cases f g x
      rfl
    have hz : (0 : ℝ) ∈ (s.image d).shadow := by
      apply (mem_shadow_iff_internal_ball hU (s.image d) 0).mpr
      intro ε hε
      obtain ⟨x, hx, hfg⟩ := h ε hε
      refine ⟨app d x, ?_, ?_⟩
      · rw [coe_image]
        exact ⟨x, hx, rfl⟩
      · rw [mem_starSet_ball_iff_starDist, hd, starDist_starDist_zero]
        exact hfg
    obtain ⟨y, hy, hy0⟩ := hz
    rw [coe_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hd, near_starDist_zero_iff] at hy0
    exact ⟨x, hx, hy0⟩

/-- If no internal argument gives infinitely close values, one positive standard distance
separates the values at every internal argument. -/
theorem not_exists_near_iff (hU : (U : Filter ℕ) ≤ atTop) (s : InternalSet U α)
    (f g : Star U (α → β)) :
    (¬ ∃ x ∈ s, Near (app f x) (app g x)) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, std ε ≤ starDist (app f x) (app g x) := by
  rw [exists_near_iff hU]
  push Not
  rfl

end Reeken.NSA.InternalSet
