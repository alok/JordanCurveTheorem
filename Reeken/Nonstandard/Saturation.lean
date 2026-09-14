import Reeken.Nonstandard.Hyperfinite
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.Finite

/-!
# Countable saturation and overspill

Saturation is proved by a diagonal choice on `ℕ`, using a free ultrafilter. No saturation
axiom is added. The conclusion concerns internal sets; arbitrary external sets are excluded.
-/

open Filter

namespace Reeken.NSA

variable {α : Type*} [Nonempty α]

/-- Diagonal realization works for every ultrafilter on naturals containing all tails.
No property of mathlib's particular choice of `hyperfilter` is used. -/
theorem countable_saturation_of_le_atTop (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∀ᶠ i in U, ∃ a, ∀ k ≤ n, P k i a) :
    ∃ x : Star U α, ∀ k, Holds (P k) x := by
  classical
  let feasible (i n : ℕ) : Prop := ∃ a, ∀ k ≤ n, P k i a
  let rank (i : ℕ) : ℕ := Nat.findGreatest (feasible i) i
  let x (i : ℕ) : α :=
    if hi : feasible i (rank i) then Classical.choose hi else Classical.arbitrary α
  refine ⟨ofSeq x, ?_⟩
  intro k
  have hk : ∀ᶠ i in U, k ≤ i := hU (eventually_ge_atTop k)
  filter_upwards [hk, h k] with i hki hi
  have hr : k ≤ rank i := Nat.le_findGreatest hki hi
  have hf : feasible i (rank i) := Nat.findGreatest_spec hki hi
  change P k i (x i)
  simp only [x, dif_pos hf]
  exact Classical.choose_spec hf k hr

/-- The chosen concrete model is an instance of the ultrafilter-independent construction. -/
theorem countable_saturation_of_eventually (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ a, ∀ k ≤ n, P k i a) :
    ∃ x : Star (hyperfilter ℕ) α, ∀ k, Holds (P k) x :=
  countable_saturation_of_le_atTop (hyperfilter ℕ) Nat.hyperfilter_le_atTop P h

/-- Countable saturation in the intrinsic finite-intersection formulation. -/
theorem countable_saturation (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∃ x : Star (hyperfilter ℕ) α, ∀ k ≤ n, Holds (P k) x) :
    ∃ x : Star (hyperfilter ℕ) α, ∀ k, Holds (P k) x := by
  apply countable_saturation_of_eventually
  intro n
  obtain ⟨x, hx⟩ := h n
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  have hall : ∀ᶠ i in hyperfilter ℕ, ∀ k ∈ Finset.range (n + 1), P k i (x i) :=
    (Finset.eventually_all _).mpr fun k hk ↦ hx k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  exact hall.mono fun i hi ↦ ⟨x i, fun k hk ↦ hi k (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))⟩

/-- A hypernatural is unlimited when it exceeds each standard natural. -/
def Unlimited (N : Hypernat) : Prop := ∀ n : ℕ, std n < N

theorem infiniteIndex_unlimited : Unlimited infiniteIndex := std_lt_infiniteIndex

/-- An internal property holding at every standard natural also holds at an unlimited one. -/
theorem overspill (P : ℕ → ℕ → Prop)
    (h : ∀ n : ℕ, Holds (U := hyperfilter ℕ) P (std n)) :
    ∃ N : Hypernat, Unlimited N ∧ Holds P N := by
  let Q (k i n : ℕ) : Prop := P i n ∧ k < n
  have hfinite : ∀ n, ∃ x : Hypernat, ∀ k ≤ n, Holds (Q k) x := by
    intro n
    refine ⟨std (n + 1), ?_⟩
    intro k hk
    exact (h (n + 1)).mono fun i hi ↦ ⟨hi, Nat.lt_succ_of_le hk⟩
  obtain ⟨N, hN⟩ := countable_saturation Q hfinite
  refine ⟨N, ?_, ?_⟩
  · intro n
    obtain ⟨N, rfl⟩ := ofSeq_surjective N
    apply (Germ.coe_lt (φ := hyperfilter ℕ)).mpr
    exact (hN n).mono fun i hi ↦ hi.2
  · obtain ⟨N, rfl⟩ := ofSeq_surjective N
    exact (hN 0).mono fun i hi ↦ hi.1

end Reeken.NSA
