import Reeken.Nonstandard.InternalSet
import Reeken.Nonstandard.Metric

/-!
# Monads, shadows, and deep regions without representatives

These definitions and compactness arguments work over every ultrafilter. Countable
saturation is needed later to prove that shadows are closed, not for the monad argument
which puts a whole compact standard set inside an internal region.
-/

open Filter Set

namespace Reeken.NSA

variable {ι α : Type*} {U : Ultrafilter ι} [PseudoMetricSpace α]

omit [PseudoMetricSpace α] in
/-- Standard set inclusion persists for all internal points. -/
theorem starSet_mono {s t : Set α} (h : s ⊆ t) : starSet (U := U) s ⊆ starSet t := by
  intro x hx
  exact holds_mono (P := fun _ a ↦ a ∈ s) (Q := fun _ a ↦ a ∈ t)
    (Eventually.of_forall fun _ _ ha ↦ h ha) hx

/-- Internal membership in a standard ball is the corresponding lifted distance bound. -/
theorem mem_starSet_ball (x : Star U α) (a : α) (ε : ℝ) :
    x ∈ starSet (Metric.ball a ε) ↔ Germ.LiftRel (fun x y ↦ dist x y < ε) x (std a) := by
  star_cases x
  rfl

/-- The monad of a standard point consists of all internal points infinitely close to it. -/
def monad (a : α) : Set (Star U α) := {x | Near x (std a)}

namespace InternalSet

/-- The standard shadow of an internal set. This is generally an external set. -/
def shadow (s : InternalSet U α) : Set α := {a | ∃ x ∈ s.toSet, Near x (std a)}

/-- A standard point is deep in an internal set when its monad avoids the complement. -/
def deep (s : InternalSet U α) : Set α := s.compl.shadowᶜ

theorem mem_deep_iff (s : InternalSet U α) (a : α) :
    a ∈ s.deep ↔ monad a ⊆ s.toSet := by
  classical
  simp only [deep, shadow, monad, mem_compl_iff, mem_ofPred_eq, coe_compl,
    not_exists, not_and, Set.subset_def]
  exact forall_congr' fun x ↦ ⟨fun h hx ↦ by_contra fun hn ↦ h hn hx,
    fun h hn hx ↦ hn (h hx)⟩

theorem std_mem_of_mem_deep {s : InternalSet U α} {a : α} (ha : a ∈ s.deep) :
    std a ∈ s :=
  (mem_deep_iff s a).mp ha (Near.refl _)

theorem shadow_mono {s t : InternalSet U α} (h : s.toSet ⊆ t.toSet) :
    s.shadow ⊆ t.shadow := by
  rintro a ⟨x, hx, ha⟩
  exact ⟨x, h hx, ha⟩

theorem deep_mono {s t : InternalSet U α} (h : s.toSet ⊆ t.toSet) :
    s.deep ⊆ t.deep := by
  intro a ha
  exact (mem_deep_iff t a).mpr (((mem_deep_iff s a).mp ha).trans h)

/-- Compactness extends standard inclusion in a deep region to all internal points. -/
theorem starSet_subset_of_isCompact {K : Set α} (hK : IsCompact K)
    {s : InternalSet U α} (hsub : K ⊆ s.deep) : starSet K ⊆ s.toSet := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := compact_standard_part hK hx
  exact (mem_deep_iff s a).mp (hsub ha) hxa

end InternalSet
end Reeken.NSA
