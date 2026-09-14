import Reeken.Nonstandard.InternalSet
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

/-- An internal finite set may have an unlimited internal cardinality. -/
abbrev Hyperfinite (U : Ultrafilter ι) (α : Type*) := Star U (Finset α)

/-- Forget internal finiteness while preserving the internal set. -/
def Hyperfinite.toInternalSet (s : Hyperfinite U α) : InternalSet U α :=
  map (fun t : Finset α ↦ (t : Set α)) s

/-- The hyperfinite set represented by the finite sets `s i`. -/
def hyperfiniteSet (s : ι → Finset α) : Set (Star U α) :=
  InternalSet.toSet (Hyperfinite.toInternalSet (ofSeq s))

@[simp] theorem mem_hyperfiniteSet_ofSeq (s : ι → Finset α) (x : ι → α) :
    ofSeq (U := U) x ∈ hyperfiniteSet s ↔ ∀ᶠ i in U, x i ∈ s i := Iff.rfl

/-- An internal function attains its maximum on an internally finite nonempty set. -/
theorem Hyperfinite.exists_max [Nonempty α] [LinearOrder β] (s : Hyperfinite U α)
    (f : Star U (α → β)) (hs : s.toInternalSet.toSet.Nonempty) :
    ∃ x ∈ s.toInternalSet, ∀ y ∈ s.toInternalSet, app f y ≤ app f x := by
  star_cases s f
  have hnonempty : ∀ᶠ i in U, (s i).Nonempty := (internalSet_nonempty _).mp hs
  have hmax : ∀ᶠ i in U, ∃ x, x ∈ s i ∧ ∀ y ∈ s i, f i y ≤ f i x :=
    hnonempty.mono fun i hi ↦ (s i).exists_max_image (f i) hi
  obtain ⟨x, hx⟩ := (exists_holds (U := U) _).mpr hmax
  star_cases x
  refine ⟨ofSeq x, hx.mono fun i hi ↦ hi.1, ?_⟩
  intro y hy
  star_cases y
  exact (hx.and hy).mono fun i hi ↦ hi.1.2 (y i) hi.2

/-- Minimum transfer is maximum transfer in the dual order. -/
theorem Hyperfinite.exists_min [Nonempty α] [LinearOrder β] (s : Hyperfinite U α)
    (f : Star U (α → β)) (hs : s.toInternalSet.toSet.Nonempty) :
    ∃ x ∈ s.toInternalSet, ∀ y ∈ s.toInternalSet, app f x ≤ app f y := by
  obtain ⟨x, hx, hmax⟩ := Hyperfinite.exists_max (β := OrderDual β) s f hs
  refine ⟨x, hx, fun y hy ↦ ?_⟩
  have h := hmax y hy
  star_cases f x y
  exact h

/-- The representative form used by finite geometric constructions. -/
theorem hyperfinite_max [Nonempty α] [LinearOrder β] (s : ι → Finset α)
    (f : ι → α → β) (hs : (hyperfiniteSet (U := U) s).Nonempty) :
    ∃ x ∈ hyperfiniteSet (U := U) s, ∀ y ∈ hyperfiniteSet s,
      app (ofSeq f) y ≤ app (ofSeq f) x :=
  Hyperfinite.exists_max (ofSeq s) (ofSeq f) hs

/-- The representative form of internal minimum transfer. -/
theorem hyperfinite_min [Nonempty α] [LinearOrder β] (s : ι → Finset α)
    (f : ι → α → β) (hs : (hyperfiniteSet (U := U) s).Nonempty) :
    ∃ x ∈ hyperfiniteSet (U := U) s, ∀ y ∈ hyperfiniteSet s,
      app (ofSeq f) x ≤ app (ofSeq f) y :=
  Hyperfinite.exists_min (ofSeq s) (ofSeq f) hs

/-- Transferred induction, restricted to an internal family of predicates. -/
theorem internal_induction (P : ι → ℕ → Prop)
    (hzero : Holds (U := U) P (std 0))
    (hstep : ∀ n : Star U ℕ, Holds P n → Holds P (map Nat.succ n)) :
    ∀ n : Star U ℕ, Holds P n := by
  star_transfer at hzero hstep ⊢
  exact (hzero.and hstep).mono fun i hi n ↦ Nat.rec hi.1 (fun k hk ↦ hi.2 k hk) n

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
  star_cases n
  simp only [mem_hyperfiniteSet_ofSeq, Finset.mem_range, Nat.lt_succ_iff, Set.mem_ofPred_eq]
  exact Germ.coe_le.symm

end Reeken.NSA
