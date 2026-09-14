import Reeken.Nonstandard.InternalSet

/-!
# Internal products

The ultrapower of a product is equivalent to the product of the ultrapowers. Pairing,
projection, and internal Cartesian products can therefore be used without choosing
representatives. The reduction rules also belong to `star_transfer`.
-/

open Filter Set

attribute [star_transfer] Set.mem_prod

namespace Reeken.NSA

variable {ι α β γ : Type*} {U : Ultrafilter ι}

@[simp, star_transfer] theorem map_map (f : β → γ) (g : α → β) (x : Star U α) :
    map f (map g x) = map (fun a ↦ f (g a)) x := by
  star_cases x
  rfl

@[simp, star_transfer] theorem max_map_map [Max β] (f g : α → β) (x : Star U α) :
    max (map f x) (map g x) = map (fun a ↦ max (f a) (g a)) x := by
  star_cases x
  rfl

/-- Pair two internal points. -/
def pair (x : Star U α) (y : Star U β) : Star U (α × β) := Germ.map₂ Prod.mk x y

@[simp, star_transfer] theorem pair_ofSeq (x : ι → α) (y : ι → β) :
    pair (ofSeq (U := U) x) (ofSeq y) = ofSeq (fun i ↦ (x i, y i)) := rfl

@[simp, star_transfer] theorem pair_std (x : α) (y : β) :
    pair (std (U := U) x) (std y) = std (x, y) := rfl

@[simp, star_transfer] theorem map_fst_pair (x : Star U α) (y : Star U β) :
    map Prod.fst (pair x y) = x := by
  star_cases x y
  rfl

@[simp, star_transfer] theorem map_snd_pair (x : Star U α) (y : Star U β) :
    map Prod.snd (pair x y) = y := by
  star_cases x y
  rfl

@[simp, star_transfer] theorem pair_fst_snd (x : Star U (α × β)) :
    pair (map Prod.fst x) (map Prod.snd x) = x := by
  star_cases x
  rfl

/-- Decompose an internal pair without passing to representatives. -/
theorem exists_pair (x : Star U (α × β)) :
    ∃ a : Star U α, ∃ b : Star U β, x = pair a b :=
  ⟨map Prod.fst x, map Prod.snd x, (pair_fst_snd x).symm⟩

theorem map_pair (f : α → β × γ) (x : Star U α) :
    map f x = pair (map (fun a ↦ (f a).1) x) (map (fun a ↦ (f a).2) x) := by
  star_cases x
  rfl

@[simp, star_transfer] theorem map_diag (f : α → β) (x : Star U α) :
    map (fun a ↦ (f a, f a)) x = pair (map f x) (map f x) := map_pair _ _

/-- Finite products commute with the ultrapower construction. -/
def prodEquiv : Star U (α × β) ≃ Star U α × Star U β where
  toFun x := (map Prod.fst x, map Prod.snd x)
  invFun x := pair x.1 x.2
  left_inv := pair_fst_snd
  right_inv x := by simp

namespace InternalSet

/-- The Cartesian product of two internal sets. -/
def prod (s : InternalSet U α) (t : InternalSet U β) : InternalSet U (α × β) :=
  Germ.map₂ Set.prod s t

@[simp, star_transfer] theorem prod_ofSeq (s : ι → Set α) (t : ι → Set β) :
    prod (ofSeq (U := U) s) (ofSeq t) = ofSeq (fun i ↦ s i ×ˢ t i) := rfl

@[simp, star_transfer] theorem mem_prod (s : InternalSet U α) (t : InternalSet U β)
    (x : Star U (α × β)) :
    x ∈ s.prod t ↔ map Prod.fst x ∈ s ∧ map Prod.snd x ∈ t := by
  star_cases s t x
  exact Filter.eventually_and

@[simp, star_transfer] theorem pair_mem_prod (s : InternalSet U α) (t : InternalSet U β)
    (x : Star U α) (y : Star U β) : pair x y ∈ s.prod t ↔ x ∈ s ∧ y ∈ t := by
  simp

/-- Under the product equivalence, internal membership is componentwise membership. -/
theorem coe_prod (s : InternalSet U α) (t : InternalSet U β) :
    (s.prod t).toSet = prodEquiv ⁻¹' (s.toSet ×ˢ t.toSet) := by
  ext x
  exact mem_prod s t x

end InternalSet
end Reeken.NSA
