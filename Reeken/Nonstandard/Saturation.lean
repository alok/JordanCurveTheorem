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

/-- Intrinsic finite-intersection saturation over any free ultrafilter on naturals. -/
theorem countable_saturation_internal_of_le_atTop (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∃ x : Star U α, ∀ k ≤ n, Holds (P k) x) :
    ∃ x : Star U α, ∀ k, Holds (P k) x := by
  apply countable_saturation_of_le_atTop U hU
  intro n
  obtain ⟨x, hx⟩ := h n
  star_cases x
  have hall : ∀ᶠ i in U, ∀ k ∈ Finset.range (n + 1), P k i (x i) :=
    (Finset.eventually_all _).mpr fun k hk ↦ hx k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  exact hall.mono fun i hi ↦ ⟨x i, fun k hk ↦ hi k (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))⟩

/-- Countable saturation for the concrete model used in the geometric construction. -/
theorem countable_saturation (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∃ x : Star (hyperfilter ℕ) α, ∀ k ≤ n, Holds (P k) x) :
    ∃ x : Star (hyperfilter ℕ) α, ∀ k, Holds (P k) x :=
  countable_saturation_internal_of_le_atTop (hyperfilter ℕ) Nat.hyperfilter_le_atTop P h

/-- A countable family of internal sets with the finite-intersection property has a point
in their intersection. No representing families occur in the statement. -/
theorem InternalSet.countable_saturation {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → InternalSet U α)
    (h : ∀ n, ∃ x : Star U α, ∀ k ≤ n, x ∈ s k) :
    ∃ x : Star U α, ∀ k, x ∈ s k := by
  classical
  choose f hf using fun n ↦ ofSeq_surjective (s n)
  have hfinite : ∀ n, ∃ x : Star U α, ∀ k ≤ n, Holds (fun i a ↦ a ∈ f k i) x := by
    intro n
    obtain ⟨x, hx⟩ := h n
    refine ⟨x, fun k hk ↦ ?_⟩
    have hmem := hx k hk
    rw [← hf k] at hmem
    exact hmem
  obtain ⟨x, hx⟩ := countable_saturation_internal_of_le_atTop U hU _ hfinite
  refine ⟨x, fun k ↦ ?_⟩
  rw [← hf k]
  exact hx k

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
    star_cases N
    apply (Germ.coe_lt (φ := hyperfilter ℕ)).mpr
    exact (hN n).mono fun i hi ↦ hi.2
  · star_cases N
    exact (hN 0).mono fun i hi ↦ hi.1

/-- An internal set containing all standard naturals contains an unlimited hypernatural. -/
theorem InternalSet.overspill (s : InternalSet (hyperfilter ℕ) ℕ)
    (h : ∀ n : ℕ, std n ∈ s) : ∃ N : Hypernat, Unlimited N ∧ N ∈ s := by
  star_cases s
  exact NSA.overspill (fun i n ↦ n ∈ s i) h

/-- The standard naturals form an external set. This also records the limit of transfer:
quantification over standard points cannot be substituted for internal quantification. -/
theorem standard_naturals_external :
    ¬ ∃ s : InternalSet (hyperfilter ℕ) ℕ, s.toSet = Set.range (std : ℕ → Hypernat) := by
  rintro ⟨s, hs⟩
  have hstd (n : ℕ) : std n ∈ s := by
    change std n ∈ s.toSet
    rw [hs]
    exact Set.mem_range_self n
  obtain ⟨N, hN, hNs⟩ := s.overspill hstd
  have hNr : N ∈ Set.range (std : ℕ → Hypernat) := by
    rw [← hs]
    exact hNs
  obtain ⟨n, rfl⟩ := hNr
  exact lt_irrefl _ (hN n)

end Reeken.NSA
