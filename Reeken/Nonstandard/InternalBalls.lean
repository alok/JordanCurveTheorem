import Reeken.Nonstandard.Hypermetric
import Reeken.Nonstandard.Shadow

/-!
# Internal balls and deep membership

Balls have internal centers and internal radii. A positive standard-radius ball inside
an internal set makes its center deep: the entire monad belongs to the set. This step
works over every ultrafilter; obtaining a standard radius from shadow exclusion uses
countable saturation and explicitly assumes a free ultrafilter on naturals.
-/

open Filter Set

attribute [star_transfer] Metric.mem_ball

namespace Reeken.NSA.InternalSet

variable {ι α : Type*} {U : Ultrafilter ι} [PseudoMetricSpace α]

/-- A ball with an internal center and internal radius. -/
def ball (a : Star U α) (r : Star U ℝ) : InternalSet U α := Germ.map₂ Metric.ball a r

@[simp, star_transfer] theorem ball_ofSeq (a : ι → α) (r : ι → ℝ) :
    ball (ofSeq (U := U) a) (ofSeq r) = ofSeq (fun i ↦ Metric.ball (a i) (r i)) := rfl

@[simp, star_transfer] theorem coe_ball_std (a : α) (r : ℝ) :
    (ball (std (U := U) a) (std r)).toSet = starSet (Metric.ball a r) := rfl

@[star_transfer] theorem mem_ball (a x : Star U α) (r : Star U ℝ) :
    x ∈ ball a r ↔ starDist x a < r := by
  star_cases a x r
  exact (ofSeq_lt (fun i ↦ dist (x i) (a i)) r).symm

/-- An appreciable internal ball contained in a set contains the whole monad of its center. -/
theorem isDeep_of_ball_subset {s : InternalSet U α} {x : Star U α} {δ : ℝ}
    (hδ : 0 < δ) (hball : (ball x (std δ)).toSet ⊆ s.toSet) : s.IsDeep x := by
  intro y hy
  exact hball ((mem_ball x y (std δ)).mpr ((near_iff_starDist y x).mp hy δ hδ))

end Reeken.NSA.InternalSet

namespace Reeken.NSA.InternalSet

variable {α : Type*} [MetricSpace α] [Nonempty α] {U : Ultrafilter ℕ}

/-- Shadow exclusion is equivalent to a positive standard lower bound on internal distances. -/
theorem not_mem_shadow_iff_starDist (hU : (U : Filter ℕ) ≤ atTop)
    (s : InternalSet U α) (a : α) :
    a ∉ s.shadow ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, std δ ≤ starDist x (std a) := by
  rw [mem_shadow_iff_internal_ball hU]
  simp only [Set.Nonempty, Set.mem_inter_iff, mem_starSet_ball_iff_starDist]
  push Not
  rfl

end Reeken.NSA.InternalSet
