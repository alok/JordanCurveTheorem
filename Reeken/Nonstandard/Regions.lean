import Reeken.Nonstandard.InternalSeparation

/-!
# Standard regions away from an internal boundary

An internal separation by two open sets induces two disjoint open standard regions
away from the boundary's shadow. This transfer step does not assert nonemptiness or
connectedness of the standard regions: those require the geometric parts of Reeken's proof.
-/

open Filter Metric Set

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E]

/-- A standard point is deep in an internal set if its whole monad avoids the complement. -/
def deep (s : ℕ → Set E) : Set E := InternalSet.deep (ofSeq (U := hyperfilter ℕ) s)

/-- Deep membership is inclusion of the whole monad, including its nonstandard points. -/
theorem mem_deep_iff_monad_subset (s : ℕ → Set E) (a : E) :
    a ∈ deep s ↔ monad (U := hyperfilter ℕ) a ⊆ internalSet s :=
  InternalSet.mem_deep_iff (ofSeq s) a

theorem mem_deep_iff (s : ℕ → Set E) (a : E) :
    a ∈ deep s ↔ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ i in hyperfilter ℕ, ∀ x ∉ s i, ε ≤ dist x a :=
  not_mem_shadow_iff _ _

theorem isOpen_deep (s : ℕ → Set E) : IsOpen (deep s) :=
  (isClosed_shadow _).isOpen_compl

theorem eventually_mem_of_mem_deep {s : ℕ → Set E} {a : E} (ha : a ∈ deep s) :
    ∀ᶠ i in hyperfilter ℕ, a ∈ s i :=
  InternalSet.std_mem_of_mem_deep ha

theorem shadow_mono {s t : ℕ → Set E} (h : ∀ᶠ i in hyperfilter ℕ, s i ⊆ t i) :
    shadow s ⊆ shadow t :=
  InternalSet.shadow_mono ((internalSet_subset s t).mpr h)

variable [NormedSpace ℝ E]

/-- Standard membership away from an internal boundary implies deep membership. -/
theorem mem_deep_of_separation {u v b : ℕ → Set E} {a : E}
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (b i)ᶜ)
    (ha : ∀ᶠ i in hyperfilter ℕ, a ∈ u i) (hb : a ∉ shadow b) : a ∈ deep u := by
  have hs : InternalSet.Separates (ofSeq u) (ofSeq v) (ofSeq b) := hsep
  exact hs.mem_deep_of_not_mem_shadow Nat.hyperfilter_le_atTop ha hb

omit [NormedSpace ℝ E] in
/-- Deep regions are disjoint whenever the underlying internal regions are disjoint. -/
theorem disjoint_deep {u v : ℕ → Set E}
    (h : ∀ᶠ i in hyperfilter ℕ, Disjoint (u i) (v i)) : Disjoint (deep u) (deep v) := by
  exact InternalSet.disjoint_deep ((InternalSet.disjoint_ofSeq_iff u v).mpr h)

/-- An internal separation exhausts precisely the standard complement of its boundary's shadow. -/
theorem deep_union_of_separation {u v b : ℕ → Set E}
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (b i)ᶜ) :
    deep u ∪ deep v = (shadow b)ᶜ := by
  have hs : InternalSet.Separates (ofSeq u) (ofSeq v) (ofSeq b) := hsep
  exact hs.deep_union Nat.hyperfilter_le_atTop

end Reeken.NSA
