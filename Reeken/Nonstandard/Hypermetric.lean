import Reeken.Nonstandard.InternalMetric
import Reeken.Nonstandard.Products

/-!
# Internal distances

The distance between internal points is an internal real. Infinitesimal closeness says
that this distance is smaller than every positive standard real; it remains an external
predicate. No real-valued metric or topology is imposed on the ultrapower.
-/

open Filter

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι} [PseudoMetricSpace α]

/-- The internal real-valued extension of the distance function. -/
def starDist (x y : Star U α) : Star U ℝ := Germ.map₂ dist x y

@[simp, star_transfer] theorem starDist_ofSeq (x y : ι → α) :
    starDist (ofSeq (U := U) x) (ofSeq y) = ofSeq (fun i ↦ dist (x i) (y i)) := rfl

@[simp, star_transfer] theorem starDist_std (x y : α) :
    starDist (std (U := U) x) (std y) = std (dist x y) := rfl

@[simp, star_transfer] theorem starDist_map_map {γ : Type*} (f g : γ → α)
    (x : Star U γ) :
    starDist (map f x) (map g x) = map (fun a ↦ dist (f a) (g a)) x := by
  star_cases x
  rfl

theorem starDist_nonneg (x y : Star U α) : std 0 ≤ starDist x y := by
  star_cases x y
  exact Germ.coe_le.mpr (Eventually.of_forall fun _ ↦ dist_nonneg)

theorem starDist_comm (x y : Star U α) : starDist x y = starDist y x := by
  star_cases x y
  exact ofSeq_eq.mpr (Eventually.of_forall fun _ ↦ dist_comm _ _)

theorem starDist_lt_std_iff (x y : Star U α) (ε : ℝ) :
    starDist x y < std ε ↔ Germ.LiftRel (fun a b ↦ dist a b < ε) x y := by
  star_cases x y
  exact Germ.coe_lt

/-- Membership in an internal ball, expressed using its internal distance. -/
theorem mem_starSet_ball_iff_starDist (x : Star U α) (a : α) (ε : ℝ) :
    x ∈ starSet (Metric.ball a ε) ↔ starDist x (std a) < std ε :=
  (mem_starSet_ball x a ε).trans (starDist_lt_std_iff x (std a) ε).symm

@[simp] theorem starDist_starDist_zero (x y : Star U α) :
    starDist (starDist x y) (std 0) = starDist x y := by
  star_cases x y
  apply ofSeq_eq.mpr
  exact Eventually.of_forall fun _ ↦ by
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]

/-- The external quantifier over standard scales is preserved. -/
theorem near_iff_starDist (x y : Star U α) :
    Near x y ↔ ∀ ε : ℝ, 0 < ε → starDist x y < std ε := by
  star_cases x y
  exact ⟨fun h ε hε ↦ Germ.coe_lt.mpr (h ε hε),
    fun h ε hε ↦ Germ.coe_lt.mp (h ε hε)⟩

/-- An internal distance is infinitesimal exactly when its endpoints are infinitely close. -/
theorem near_starDist_zero_iff (x y : Star U α) :
    Near (starDist x y) (std 0) ↔ Near x y := by
  star_cases x y
  change Near (ofSeq (fun i ↦ dist (x i) (y i))) (ofSeq (fun _ ↦ (0 : ℝ))) ↔ _
  simp only [near_ofSeq,
    Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]

variable [PseudoMetricSpace β]

@[simp, star_transfer] theorem starDist_pair (x x' : Star U α) (y y' : Star U β) :
    starDist (pair x y) (pair x' y') = max (starDist x x') (starDist y y') := by
  star_cases x x' y y'
  rfl

@[simp] theorem near_pair_iff (x x' : Star U α) (y y' : Star U β) :
    Near (pair x y) (pair x' y') ↔ Near x x' ∧ Near y y' := by
  star_cases x x' y y'
  simp only [pair_ofSeq, near_ofSeq, Prod.dist_eq, max_lt_iff, Filter.eventually_and]
  exact ⟨fun h ↦ ⟨fun ε hε ↦ (h ε hε).1, fun ε hε ↦ (h ε hε).2⟩,
    fun h ε hε ↦ ⟨h.1 ε hε, h.2 ε hε⟩⟩

/-- An internal pair is infinitely close precisely when both coordinates are. -/
theorem near_prod_iff (x y : Star U (α × β)) :
    Near x y ↔ Near (map Prod.fst x) (map Prod.fst y) ∧
      Near (map Prod.snd x) (map Prod.snd y) := by
  rw [← pair_fst_snd x, ← pair_fst_snd y, near_pair_iff]
  simp only [map_fst_pair, map_snd_pair]

/-- Shadows commute with internal Cartesian products, without a saturation hypothesis. -/
theorem InternalSet.shadow_prod (s : InternalSet U α) (t : InternalSet U β) :
    (s.prod t).shadow = s.shadow ×ˢ t.shadow := by
  ext a
  constructor
  · rintro ⟨x, hx, ha⟩
    have hm := (InternalSet.mem_prod s t x).mp hx
    have hn := (near_prod_iff x (std a)).mp ha
    exact ⟨⟨map Prod.fst x, hm.1, by simpa only [map_std] using hn.1⟩,
      ⟨map Prod.snd x, hm.2, by simpa only [map_std] using hn.2⟩⟩
  · rintro ⟨⟨x, hx, hxa⟩, ⟨y, hy, hya⟩⟩
    refine ⟨pair x y, (InternalSet.pair_mem_prod s t x y).mpr ⟨hx, hy⟩, ?_⟩
    rw [← pair_std a.1 a.2, near_pair_iff]
    exact ⟨hxa, hya⟩

end Reeken.NSA
