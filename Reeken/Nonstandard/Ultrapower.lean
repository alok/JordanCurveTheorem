import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Ultrapowers and internal predicates

The extension is a genuine quotient of sequences modulo an ultrafilter. Internal predicates
are indexed families of ordinary predicates, not arbitrary predicates on the quotient.
The quantifier lemmas below prove the transfer rules needed for internal constructions.
-/

open Filter

namespace Reeken.NSA

universe u v w

variable {ι : Type u} {α : Type v} {β : Type w}

/-- The extension of a type over the ultrafilter `U`. -/
abbrev Star (U : Ultrafilter ι) (α : Type v) := Germ (U : Filter ι) α

variable {U : Ultrafilter ι}

/-- The class of an indexed family. -/
def ofSeq (f : ι → α) : Star U α := Germ.ofFun f

/-- The embedding of standard objects. -/
def std (a : α) : Star U α := Germ.const a

theorem ofSeq_surjective : Function.Surjective (ofSeq (U := U) : (ι → α) → Star U α) :=
  Quot.exists_rep

@[simp] theorem ofSeq_eq {f g : ι → α} :
    ofSeq (U := U) f = ofSeq g ↔ ∀ᶠ i in U, f i = g i := Germ.coe_eq

@[simp] theorem std_inj {a b : α} : (std a : Star U α) = std b ↔ a = b :=
  Germ.const_inj

/-- Extend an ordinary function. -/
def map (f : α → β) : Star U α → Star U β := Germ.map f

@[simp] theorem map_ofSeq (f : α → β) (x : ι → α) :
    map f (ofSeq (U := U) x) = ofSeq (fun i ↦ f (x i)) := rfl

@[simp] theorem map_std (f : α → β) (x : α) :
    map f (std x : Star U α) = std (f x) := rfl

/-- Apply an internal function to an internal argument. -/
def app : Star U (α → β) → Star U α → Star U β := Germ.map₂ (fun f x ↦ f x)

@[simp] theorem app_ofSeq (f : ι → α → β) (x : ι → α) :
    app (ofSeq (U := U) f) (ofSeq x) = ofSeq (fun i ↦ f i (x i)) := rfl

/-- Interpret an internal predicate at a quotient element. -/
def Holds (P : ι → α → Prop) (x : Star U α) : Prop :=
  x.liftOn (fun f ↦ ∀ᶠ i in U, P i (f i))
    (fun f g h ↦ propext (Filter.eventually_congr (h.mono fun i hi ↦ by rw [hi])))

@[simp] theorem holds_ofSeq (P : ι → α → Prop) (x : ι → α) :
    Holds (U := U) P (ofSeq x) ↔ ∀ᶠ i in U, P i (x i) := Iff.rfl

@[simp] theorem holds_std (P : α → Prop) (a : α) :
    Holds (U := U) (fun _ ↦ P) (std a) ↔ P a := Filter.eventually_const

theorem holds_congr {P Q : ι → α → Prop}
    (h : ∀ᶠ i in U, ∀ a, P i a ↔ Q i a) (x : Star U α) :
    Holds P x ↔ Holds Q x := by
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  exact Filter.eventually_congr (h.mono fun i hi ↦ hi (x i))

theorem holds_mono {P Q : ι → α → Prop}
    (h : ∀ᶠ i in U, ∀ a, P i a → Q i a) {x : Star U α} :
    Holds P x → Holds Q x := by
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  intro hx
  exact (h.and hx).mono fun i hi ↦ hi.1 (x i) hi.2

@[simp] theorem holds_and (P Q : ι → α → Prop) (x : Star U α) :
    Holds (fun i a ↦ P i a ∧ Q i a) x ↔ Holds P x ∧ Holds Q x := by
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  exact Filter.eventually_and

@[simp] theorem holds_not (P : ι → α → Prop) (x : Star U α) :
    Holds (fun i a ↦ ¬ P i a) x ↔ ¬ Holds P x := by
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  exact Ultrafilter.eventually_not

@[simp] theorem holds_or (P Q : ι → α → Prop) (x : Star U α) :
    Holds (fun i a ↦ P i a ∨ Q i a) x ↔ Holds P x ∨ Holds Q x := by
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  exact Ultrafilter.eventually_or

@[simp] theorem holds_imp (P Q : ι → α → Prop) (x : Star U α) :
    Holds (fun i a ↦ P i a → Q i a) x ↔ (Holds P x → Holds Q x) := by
  classical
  simp only [imp_iff_not_or, holds_or, holds_not]

/-- Existential transfer chooses an internal witness, which may depend on the index. -/
theorem exists_holds [Nonempty α] (P : ι → α → Prop) :
    (∃ x : Star U α, Holds P x) ↔ ∀ᶠ i in U, ∃ a, P i a := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := ofSeq_surjective x
    exact hx.mono fun i hi ↦ ⟨x i, hi⟩
  · intro h
    let x (i : ι) : α := if hi : ∃ a, P i a then Classical.choose hi else Classical.arbitrary α
    refine ⟨ofSeq x, h.mono ?_⟩
    intro i hi
    exact (show P i (x i) by simp only [x, dif_pos hi]; exact Classical.choose_spec hi)

/-- Universal transfer quantifies over all internal elements, including nonstandard ones. -/
theorem forall_holds [Nonempty α] (P : ι → α → Prop) :
    (∀ x : Star U α, Holds P x) ↔ ∀ᶠ i in U, ∀ a, P i a := by
  classical
  apply not_iff_not.mp
  rw [not_forall, ← Ultrafilter.eventually_not]
  simp only [not_forall, ← holds_not]
  exact exists_holds (U := U) (fun i a ↦ ¬ P i a)

/-- The internal subset represented by a family of ordinary subsets. -/
def internalSet (s : ι → Set α) : Set (Star U α) := {x | Holds (fun i a ↦ a ∈ s i) x}

/-- The star extension of a standard set. -/
def starSet (s : Set α) : Set (Star U α) := internalSet (fun _ ↦ s)

@[simp] theorem mem_internalSet_ofSeq (s : ι → Set α) (x : ι → α) :
    ofSeq (U := U) x ∈ internalSet s ↔ ∀ᶠ i in U, x i ∈ s i := Iff.rfl

@[simp] theorem std_mem_starSet (s : Set α) (a : α) :
    (std a : Star U α) ∈ starSet s ↔ a ∈ s := Filter.eventually_const

theorem internalSet_inter (s t : ι → Set α) :
    internalSet (U := U) (fun i ↦ s i ∩ t i) = internalSet s ∩ internalSet t := by
  ext x
  exact holds_and _ _ x

theorem internalSet_union (s t : ι → Set α) :
    internalSet (U := U) (fun i ↦ s i ∪ t i) = internalSet s ∪ internalSet t := by
  ext x
  exact holds_or _ _ x

theorem internalSet_compl (s : ι → Set α) :
    internalSet (U := U) (fun i ↦ (s i)ᶜ) = (internalSet s)ᶜ := by
  ext x
  exact holds_not _ x

theorem internalSet_nonempty [Nonempty α] (s : ι → Set α) :
    (internalSet (U := U) s).Nonempty ↔ ∀ᶠ i in U, (s i).Nonempty := exists_holds _

theorem internalSet_subset [Nonempty α] (s t : ι → Set α) :
    internalSet (U := U) s ⊆ internalSet t ↔ ∀ᶠ i in U, s i ⊆ t i := by
  simp only [Set.subset_def]
  change (∀ x : Star U α, Holds (fun i a ↦ a ∈ s i) x →
    Holds (fun i a ↦ a ∈ t i) x) ↔ _
  simp only [← holds_imp, forall_holds]

end Reeken.NSA
