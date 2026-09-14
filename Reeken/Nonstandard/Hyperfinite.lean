import Reeken.Nonstandard.Ultrapower
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.FilterProduct

/-!
# Hyperfinite sets and internal induction

An internal family of finite sets need not be externally finite. Extrema are obtained
by transferring the finite extremum theorem, and induction applies to internal predicates.
-/

open Filter

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι}

/-- The hyperfinite set represented by the finite sets `s i`. -/
def hyperfiniteSet (s : ι → Finset α) : Set (Star U α) := internalSet (fun i ↦ (s i : Set α))

@[simp] theorem mem_hyperfiniteSet_ofSeq (s : ι → Finset α) (x : ι → α) :
    ofSeq (U := U) x ∈ hyperfiniteSet s ↔ ∀ᶠ i in U, x i ∈ s i := Iff.rfl

/-- An internal function attains a maximum on a nonempty hyperfinite set. -/
theorem hyperfinite_max [Nonempty α] [LinearOrder β] (s : ι → Finset α)
    (f : ι → α → β) (hs : (hyperfiniteSet (U := U) s).Nonempty) :
    ∃ x ∈ hyperfiniteSet (U := U) s, ∀ y ∈ hyperfiniteSet s,
      app (ofSeq f) y ≤ app (ofSeq f) x := by
  have hnonempty : ∀ᶠ i in U, (s i).Nonempty := (internalSet_nonempty _).mp hs
  have hmax : ∀ᶠ i in U, ∃ x, x ∈ s i ∧ ∀ y ∈ s i, f i y ≤ f i x :=
    hnonempty.mono fun i hi ↦ (s i).exists_max_image (f i) hi
  obtain ⟨x, hx⟩ := (exists_holds (U := U) _).mpr hmax
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  refine ⟨ofSeq x, hx.mono fun i hi ↦ hi.1, ?_⟩
  intro y hy
  obtain ⟨y, rfl⟩ := ofSeq_surjective y
  exact (hx.and hy).mono fun i hi ↦ hi.1.2 (y i) hi.2

/-- An internal function attains a minimum on a nonempty hyperfinite set. -/
theorem hyperfinite_min [Nonempty α] [LinearOrder β] (s : ι → Finset α)
    (f : ι → α → β) (hs : (hyperfiniteSet (U := U) s).Nonempty) :
    ∃ x ∈ hyperfiniteSet (U := U) s, ∀ y ∈ hyperfiniteSet s,
      app (ofSeq f) x ≤ app (ofSeq f) y := by
  have hnonempty : ∀ᶠ i in U, (s i).Nonempty := (internalSet_nonempty _).mp hs
  have hmin : ∀ᶠ i in U, ∃ x, x ∈ s i ∧ ∀ y ∈ s i, f i x ≤ f i y :=
    hnonempty.mono fun i hi ↦ (s i).exists_min_image (f i) hi
  obtain ⟨x, hx⟩ := (exists_holds (U := U) _).mpr hmin
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  refine ⟨ofSeq x, hx.mono fun i hi ↦ hi.1, ?_⟩
  intro y hy
  obtain ⟨y, rfl⟩ := ofSeq_surjective y
  exact (hx.and hy).mono fun i hi ↦ hi.1.2 (y i) hi.2

/-- Transferred induction, restricted to an internal family of predicates. -/
theorem internal_induction (P : ι → ℕ → Prop)
    (hzero : Holds (U := U) P (std 0))
    (hstep : ∀ n : Star U ℕ, Holds P n → Holds P (map Nat.succ n)) :
    ∀ n : Star U ℕ, Holds P n := by
  have hs : ∀ n : Star U ℕ, Holds (fun i k ↦ P i k → P i (k + 1)) n := by
    intro n
    rw [holds_imp]
    obtain ⟨n, rfl⟩ := ofSeq_surjective n
    exact hstep (ofSeq n)
  have hs' := (forall_holds _).mp hs
  apply (forall_holds _).mpr
  exact (hzero.and hs').mono fun i hi n ↦ Nat.rec hi.1 (fun k hk ↦ hi.2 k hk) n

/-- The natural-number extension built over a free ultrafilter on `ℕ`. -/
abbrev Hypernat := Star (hyperfilter ℕ) ℕ

/-- The infinite hypernatural represented by the identity sequence. -/
noncomputable def infiniteIndex : Hypernat := ofSeq id

theorem std_lt_infiniteIndex (n : ℕ) : std n < infiniteIndex := by
  change ofSeq (U := hyperfilter ℕ) (fun _ ↦ n) < ofSeq id
  apply (Germ.coe_lt (φ := hyperfilter ℕ)).mpr
  exact Nat.hyperfilter_le_atTop (eventually_gt_atTop n)

/-- The interval up to an internal natural is hyperfinite, even for an infinite bound. -/
theorem hyperfinite_initial_segment (N : ι → ℕ) :
    hyperfiniteSet (U := U) (fun i ↦ Finset.range (N i + 1)) =
      {n : Star U ℕ | n ≤ ofSeq N} := by
  ext n
  obtain ⟨n, rfl⟩ := ofSeq_surjective n
  simp only [mem_hyperfiniteSet_ofSeq, Finset.mem_range, Nat.lt_succ_iff, Set.mem_ofPred_eq]
  exact Germ.coe_le.symm

end Reeken.NSA
