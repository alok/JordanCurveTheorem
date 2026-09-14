import Reeken.Nonstandard.Shadow
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

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
def deep (s : ℕ → Set E) : Set E := (shadow (fun i ↦ (s i)ᶜ))ᶜ

theorem mem_deep_iff (s : ℕ → Set E) (a : E) :
    a ∈ deep s ↔ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ i in hyperfilter ℕ, ∀ x ∉ s i, ε ≤ dist x a :=
  not_mem_shadow_iff _ _

theorem isOpen_deep (s : ℕ → Set E) : IsOpen (deep s) :=
  (isClosed_shadow _).isOpen_compl

theorem eventually_mem_of_mem_deep {s : ℕ → Set E} {a : E} (ha : a ∈ deep s) :
    ∀ᶠ i in hyperfilter ℕ, a ∈ s i := by
  obtain ⟨ε, hε, h⟩ := (mem_deep_iff s a).mp ha
  filter_upwards [h] with i hi
  by_contra hn
  have hd := hi a hn
  simp only [dist_self] at hd
  exact (not_le_of_gt hε) hd

theorem shadow_mono {s t : ℕ → Set E} (h : ∀ᶠ i in hyperfilter ℕ, s i ⊆ t i) :
    shadow s ⊆ shadow t := by
  rintro a ⟨x, hx, ha⟩
  exact ⟨x, (internalSet_subset s t).mpr h hx, ha⟩

variable [NormedSpace ℝ E]

/-- A connected ball avoiding the separating set stays on its initial side. -/
theorem ball_subset_side {u v b : Set E} {a : E} {ε : ℝ}
    (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hcover : u ∪ v = bᶜ) (hε : 0 < ε) (ha : a ∈ u)
    (hd : ∀ x ∈ b, ε ≤ dist x a) : ball a ε ⊆ u := by
  have hsub : ball a ε ⊆ u ∪ v := by
    rw [hcover]
    intro x hx hxb
    exact (not_le_of_gt hx) (hd x hxb)
  exact ((convex_ball a ε).isPreconnected).subset_left_of_subset_union
    hu hv huv hsub ⟨a, mem_ball_self hε, ha⟩

/-- Standard membership away from an internal boundary implies deep membership. -/
theorem mem_deep_of_separation {u v b : ℕ → Set E} {a : E}
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (b i)ᶜ)
    (ha : ∀ᶠ i in hyperfilter ℕ, a ∈ u i) (hb : a ∉ shadow b) : a ∈ deep u := by
  obtain ⟨ε, hε, hd⟩ := (not_mem_shadow_iff b a).mp hb
  refine (mem_deep_iff u a).mpr ⟨ε, hε, ?_⟩
  filter_upwards [hsep, ha, hd] with i hi hai hdi
  intro x hx
  apply le_of_not_gt
  intro hlt
  exact hx (ball_subset_side hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hε hai hdi hlt)

omit [NormedSpace ℝ E] in
/-- Deep regions are disjoint whenever the underlying internal regions are disjoint. -/
theorem disjoint_deep {u v : ℕ → Set E}
    (h : ∀ᶠ i in hyperfilter ℕ, Disjoint (u i) (v i)) : Disjoint (deep u) (deep v) := by
  rw [Set.disjoint_left]
  intro a ha hb
  have hfalse : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), False := by
    filter_upwards [h, eventually_mem_of_mem_deep ha, eventually_mem_of_mem_deep hb]
      with i hi hai hbi
    exact Set.disjoint_left.mp hi hai hbi
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- An internal separation exhausts precisely the standard complement of its boundary's shadow. -/
theorem deep_union_of_separation {u v b : ℕ → Set E}
    (hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧ u i ∪ v i = (b i)ᶜ) :
    deep u ∪ deep v = (shadow b)ᶜ := by
  have hbu : ∀ᶠ i in hyperfilter ℕ, b i ⊆ (u i)ᶜ := by
    filter_upwards [hsep] with i hi
    intro x hx hxu
    have hc : x ∈ (b i)ᶜ := hi.2.2.2 ▸ Or.inl hxu
    exact hc hx
  have hbv : ∀ᶠ i in hyperfilter ℕ, b i ⊆ (v i)ᶜ := by
    filter_upwards [hsep] with i hi
    intro x hx hxv
    have hc : x ∈ (b i)ᶜ := hi.2.2.2 ▸ Or.inr hxv
    exact hc hx
  ext a
  constructor
  · rintro (ha | ha) hb
    · exact ha (shadow_mono hbu hb)
    · exact ha (shadow_mono hbv hb)
  · intro hb
    obtain ⟨ε, hε, hd⟩ := (not_mem_shadow_iff b a).mp hb
    have hmem : ∀ᶠ i in hyperfilter ℕ, a ∈ u i ∨ a ∈ v i := by
      filter_upwards [hsep, hd] with i hi hdi
      have hab : a ∉ b i := by
        intro hab
        have h := hdi a hab
        simp only [dist_self] at h
        exact (not_le_of_gt hε) h
      change a ∈ u i ∪ v i
      rw [hi.2.2.2]
      exact hab
    rcases Ultrafilter.eventually_or.mp hmem with hu | hv
    · exact Or.inl (mem_deep_of_separation hsep hu hb)
    · apply Or.inr
      apply mem_deep_of_separation (v := u) (b := b) ?_ hv hb
      exact hsep.mono fun i hi ↦ ⟨hi.2.1, hi.1, hi.2.2.1.symm,
        (union_comm _ _).trans hi.2.2.2⟩

end Reeken.NSA
