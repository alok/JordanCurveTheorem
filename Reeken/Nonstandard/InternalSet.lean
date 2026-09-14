import Reeken.Nonstandard.TransferRules

/-!
# Internal sets as quotient objects

An `InternalSet U α` is itself an element of the ultrapower of `Set α`. Its elements are
internal points. Equal representatives define the same internal set, and images may be
taken under arbitrary internal functions. The indexed `internalSet` API is recovered by
`coe_ofSeq`; clients need representatives only when applying a finite theorem.
-/

open Filter Set

namespace Reeken.NSA

universe u v w
variable {ι : Type u} {α : Type v} {β : Type w} {U : Ultrafilter ι}

/-- An internal set, independent of a choice of representing family. -/
abbrev InternalSet (U : Ultrafilter ι) (α : Type v) := Star U (Set α)

namespace InternalSet

/-- The external set of internal points belonging to an internal set. -/
def toSet (s : InternalSet U α) : Set (Star U α) :=
  s.liftOn internalSet fun f g h ↦ by
    ext x
    exact holds_congr (h.mono fun i hi a ↦ by rw [hi]) x

instance : CoeTC (InternalSet U α) (Set (Star U α)) := ⟨toSet⟩
instance : Membership (Star U α) (InternalSet U α) := ⟨fun s x ↦ x ∈ toSet s⟩

@[simp, star_transfer] theorem coe_ofSeq (s : ι → Set α) :
    toSet (ofSeq (U := U) s) = internalSet s := rfl

@[simp, star_transfer] theorem mem_ofSeq (s : ι → Set α) (x : ι → α) :
    ofSeq x ∈ (ofSeq s : InternalSet U α) ↔ ∀ᶠ i in U, x i ∈ s i := Iff.rfl

@[star_transfer] theorem mem_ofSeq_iff_holds (s : ι → Set α) (x : Star U α) :
    x ∈ (ofSeq s : InternalSet U α) ↔ Holds (fun i a ↦ a ∈ s i) x := Iff.rfl

@[star_transfer] theorem mem_std_iff_holds (s : Set α) (x : Star U α) :
    x ∈ (std s : InternalSet U α) ↔ Holds (fun _ a ↦ a ∈ s) x := Iff.rfl

@[simp, star_transfer] theorem coe_std (s : Set α) :
    toSet (std (U := U) s) = starSet s := coe_ofSeq _

@[simp, star_transfer] theorem std_mem_std (s : Set α) (x : α) :
    (std x : Star U α) ∈ (std s : InternalSet U α) ↔ x ∈ s :=
  Filter.eventually_const

theorem subset_iff [Nonempty α] (s t : InternalSet U α) :
    s.toSet ⊆ t.toSet ↔ s ≤ t := by
  star_cases s t
  exact (internalSet_subset s t).trans Germ.coe_le.symm

/-- Internal sets are determined by their internal elements. -/
theorem toSet_injective [Nonempty α] :
    Function.Injective (toSet : InternalSet U α → Set (Star U α)) := by
  intro s t h
  exact le_antisymm ((subset_iff s t).mp h.subset) ((subset_iff t s).mp h.symm.subset)

/-- Internal complement. -/
def compl (s : InternalSet U α) : InternalSet U α := map Set.compl s

@[simp, star_transfer] theorem coe_compl (s : InternalSet U α) :
    s.compl.toSet = s.toSetᶜ := by
  star_cases s
  exact internalSet_compl s

@[simp, star_transfer] theorem coe_inf (s t : InternalSet U α) :
    (s ⊓ t).toSet = s.toSet ∩ t.toSet := by
  star_cases s t
  exact internalSet_inter s t

@[simp, star_transfer] theorem coe_sup (s t : InternalSet U α) :
    (s ⊔ t).toSet = s.toSet ∪ t.toSet := by
  star_cases s t
  exact internalSet_union s t

/-- The image of an internal set under an internal function. -/
def image (f : Star U (α → β)) (s : InternalSet U α) : InternalSet U β :=
  Germ.map₂ Set.image f s

@[simp, star_transfer] theorem image_ofSeq (f : ι → α → β) (s : ι → Set α) :
    image (ofSeq (U := U) f) (ofSeq s) = ofSeq (fun i ↦ f i '' s i) := rfl

/-- Existential transfer supplies preimages for every internal point of the image. -/
theorem coe_image [Nonempty α] (f : Star U (α → β)) (s : InternalSet U α) :
    (s.image f).toSet = app f '' s.toSet := by
  star_cases f s
  ext y
  constructor
  · intro hy
    star_cases y
    obtain ⟨x, hx⟩ := (exists_holds (U := U)
      (fun i x ↦ x ∈ s i ∧ f i x = y i)).mpr hy
    star_cases x
    exact ⟨ofSeq x, hx.mono fun i hi ↦ hi.1,
      ofSeq_eq.mpr (hx.mono fun i hi ↦ hi.2)⟩
  · rintro ⟨x, hx, rfl⟩
    star_cases x
    exact hx.mono fun i hi ↦ ⟨x i, hi, rfl⟩

end InternalSet

end Reeken.NSA
