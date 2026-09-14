import Reeken.Nonstandard.Transfer
import Mathlib.Order.Filter.FilterProduct

/-! # Rules for internal transfer normalization

Boolean combinations are collected into one internal predicate before quantifier transfer.
This orientation is intentionally different from ordinary `simp`, which exposes the Boolean
structure. Standard quantifiers are left in place; only `exists_holds` and `forall_holds`
move quantifiers over the full ultrapower.
-/

open Filter

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι}

@[star_transfer] theorem holds_map (P : ι → β → Prop) (f : α → β) (x : Star U α) :
    Holds P (map f x) ↔ Holds (fun i a ↦ P i (f a)) x := by
  star_cases x
  rfl

@[star_transfer] theorem holds_std_indexed (P : ι → α → Prop) (a : α) :
    Holds (U := U) P (std a) ↔ ∀ᶠ i in U, P i a := Iff.rfl

@[simp, star_transfer] theorem app_std (f : α → β) (x : Star U α) :
    app (std f) x = map f x := by
  star_cases x
  rfl

@[simp, star_transfer] theorem app_std_fun (f : α → β) :
    app (std (U := U) f) = map f := funext (app_std f)

@[star_transfer] theorem ofSeq_le [LE α] (x y : ι → α) :
    ofSeq (U := U) x ≤ ofSeq y ↔ ∀ᶠ i in U, x i ≤ y i := Germ.coe_le

@[star_transfer] theorem ofSeq_lt [Preorder α] (x y : ι → α) :
    ofSeq (U := U) x < ofSeq y ↔ ∀ᶠ i in U, x i < y i := Germ.coe_lt

attribute [star_transfer] ofSeq_eq std_inj map_ofSeq map_std app_ofSeq
  holds_ofSeq holds_std exists_holds forall_holds
  mem_internalSet_ofSeq std_mem_starSet internalSet_inter internalSet_union internalSet_compl
  internalSet_nonempty internalSet_subset Filter.eventually_const
attribute [star_transfer ←] holds_and holds_or holds_not holds_imp

end Reeken.NSA
