import Reeken.Nonstandard.Shadow

/-! # Internal sets contained in a single metric monad -/

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [MetricSpace E]

/-- Every point of the set is infinitesimally close to the given center. -/
def InMonad (s : Set (Star U E)) (a : Star U E) : Prop := ∀ x ∈ s, Near x a

theorem InMonad.mono {s t : Set (Star U E)} {a : Star U E}
    (ht : InMonad t a) (hst : s ⊆ t) : InMonad s a :=
  fun x hx ↦ ht x (hst hx)

theorem InMonad.union {s t : Set (Star U E)} {a : Star U E}
    (hs : InMonad s a) (ht : InMonad t a) : InMonad (s ∪ t) a := by
  intro x hx
  rcases hx with hx | hx
  · exact hs x hx
  · exact ht x hx

theorem InMonad.change_center {s : Set (Star U E)} {a b : Star U E}
    (hs : InMonad s a) (hab : Near a b) : InMonad s b :=
  fun x hx ↦ (hs x hx).trans hab

/-- Two distinct standard shadow points prevent an internal set from collapsing into one monad. -/
theorem not_inMonad_of_distinct_shadow [Nonempty E] {s : ℕ → Set E} {a b : E}
    (ha : a ∈ shadow s) (hb : b ∈ shadow s) (hab : a ≠ b)
    (c : Star (Filter.hyperfilter ℕ) E) : ¬ InMonad (internalSet s) c := by
  intro hc
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨y, hy, hyb⟩ := hb
  apply hab
  exact near_std_std.mp (hxa.symm.trans ((hc x hx).trans ((hc y hy).symm.trans hyb)))

end Reeken.NSA
