import Reeken.Nonstandard.InternalBalls
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Internal open separations

The finite assertion that two disjoint open sets cover a boundary complement is
lifted as an internal predicate. Appreciable balls stay on their initial side, so
deep membership and passage to standard parts follow from monad inclusion.
-/

open Filter Metric Set

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [NormedAddCommGroup E]

namespace InternalSet

/-- Two internal open sets are disjoint and cover the complement of the internal boundary. -/
def Separates (u v b : InternalSet U E) : Prop :=
  Holds (fun (_ : ι) (w : Set E × Set E × Set E) ↦
    IsOpen w.1 ∧ IsOpen w.2.1 ∧ Disjoint w.1 w.2.1 ∧ w.1 ∪ w.2.1 = w.2.2ᶜ)
    (pair u (pair v b))

@[simp, star_transfer] theorem separates_ofSeq (u v b : ι → Set E) :
    Separates (ofSeq (U := U) u) (ofSeq v) (ofSeq b) ↔
      ∀ᶠ i in U, IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧
        u i ∪ v i = (b i)ᶜ := Iff.rfl

theorem Separates.symm {u v b : InternalSet U E} (h : Separates u v b) :
    Separates v u b := by
  star_cases u v b
  exact h.mono fun i hi ↦ ⟨hi.2.1, hi.1, hi.2.2.1.symm,
    (union_comm _ _).trans hi.2.2.2⟩

theorem Separates.disjoint {u v b : InternalSet U E} (h : Separates u v b) :
    Disjoint u.toSet v.toSet := by
  star_cases u v b
  exact (disjoint_ofSeq_iff u v).mpr (h.mono fun i hi ↦ hi.2.2.1)

theorem Separates.cover {u v b : InternalSet U E} (h : Separates u v b) :
    u.toSet ∪ v.toSet = b.toSetᶜ := by
  star_cases u v b
  change internalSet u ∪ internalSet v = (internalSet b)ᶜ
  rw [← internalSet_union, ← internalSet_compl]
  ext x
  exact holds_congr (h.mono fun i hi a ↦ by
    have hc : u i ∪ v i = (b i)ᶜ := hi.2.2.2
    change a ∈ u i ∪ v i ↔ a ∈ (b i)ᶜ
    rw [hc]) x

end InternalSet

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

namespace InternalSet

/-- An appreciable ball avoiding the internal boundary stays in its initial region. -/
theorem Separates.ball_subset {u v b : InternalSet U E} (h : Separates u v b)
    {x : Star U E} (hx : x ∈ u) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ b, std δ ≤ starDist y x) : (ball x (std δ)).toSet ⊆ u.toSet := by
  star_cases u v b x
  star_transfer at hd
  intro y hy
  star_cases y
  have hy' : ∀ᶠ i in U, dist (y i) (x i) < δ := hy
  filter_upwards [h, hx, hd, hy'] with i hi hxi hdi hyi
  exact ball_subset_side hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hδ hxi hdi hyi

/-- Appreciable separation from the boundary makes an internal point deep on its side. -/
theorem Separates.isDeep_of_separated {u v b : InternalSet U E} (h : Separates u v b)
    {x : Star U E} (hx : x ∈ u) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ b, std δ ≤ starDist y x) : u.IsDeep x :=
  isDeep_of_ball_subset hδ (h.ball_subset hx hδ hd)

/-- A near-standard point appreciably far from the boundary has its standard part deep
in the same region, over any ultrafilter. -/
theorem Separates.standard_part_mem_deep {u v b : InternalSet U E} (h : Separates u v b)
    {x : Star U E} (hx : x ∈ u) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ b, std δ ≤ starDist y x) {a : E} (ha : Near x (std a)) : a ∈ u.deep :=
  (h.isDeep_of_separated hx hδ hd).standard_part ha

end InternalSet
end Reeken.NSA

namespace Reeken.NSA.InternalSet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Ultrafilter ℕ}

/-- Standard membership outside the boundary shadow gives deep membership. -/
theorem Separates.mem_deep_of_not_mem_shadow {u v b : InternalSet U E}
    (h : Separates u v b) (hU : (U : Filter ℕ) ≤ atTop) {a : E}
    (ha : std a ∈ u) (hb : a ∉ b.shadow) : a ∈ u.deep := by
  obtain ⟨δ, hδ, hd⟩ := (not_mem_shadow_iff_starDist hU b a).mp hb
  exact (mem_deep_iff_isDeep u a).mpr (h.isDeep_of_separated ha hδ hd)

omit [NormedSpace ℝ E] in
/-- A deep region avoids the boundary shadow, over every ultrafilter. -/
theorem Separates.deep_subset_compl_shadow {ι : Type*} {V : Ultrafilter ι}
    {u v b : InternalSet V E} (h : Separates u v b) : u.deep ⊆ b.shadowᶜ := by
  rintro a ha ⟨x, hx, hxa⟩
  have hxu := (mem_deep_iff_isDeep u a).mp ha x hxa
  have hxc : x ∈ b.toSetᶜ := h.cover ▸ Or.inl hxu
  exact hxc hx

/-- The two deep regions exhaust the complement of the boundary shadow. -/
theorem Separates.deep_union {u v b : InternalSet U E} (h : Separates u v b)
    (hU : (U : Filter ℕ) ≤ atTop) : u.deep ∪ v.deep = b.shadowᶜ := by
  apply Set.Subset.antisymm
  · exact Set.union_subset h.deep_subset_compl_shadow h.symm.deep_subset_compl_shadow
  · intro a ha
    have hnb : std a ∉ b.toSet := fun hb ↦ ha ⟨std a, hb, Near.refl _⟩
    have huv : std a ∈ u.toSet ∪ v.toSet := h.cover.symm ▸ hnb
    rcases huv with hu | hv
    · exact Or.inl (h.mem_deep_of_not_mem_shadow hU hu ha)
    · exact Or.inr (h.symm.mem_deep_of_not_mem_shadow hU hv ha)

end Reeken.NSA.InternalSet
