import Reeken.Geometry.SimpleLoop
import Schoenflies.Curve

/-! # Removing one point from a simple closed parametrized curve

This concerns the curve itself, rather than its planar complement. Cutting the
parameter circle leaves an interval, so no Jordan separation theorem is needed.
-/

open Set

namespace Reeken.Geometry

variable {E : Type*} [TopologicalSpace E]

theorem SimpleLoop.isPreconnected_punctured (f : SimpleLoop E) (z : E) :
    IsPreconnected (f '' Icc 0 1 \ {z}) := by
  by_cases hz : z ∈ f '' Icc 0 1
  · obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨t, ht, he⟩ : ∃ s ∈ Ico (0 : ℝ) 1, f s = f t := by
      by_cases ht1 : t = 1
      · exact ⟨0, ⟨le_rfl, zero_lt_one⟩, by rw [ht1, f.endpoint]⟩
      · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩, rfl⟩
    rw [← he]
    by_cases ht0 : t = 0
    · subst t
      have him : f '' Icc 0 1 \ {f 0} = f '' Ioo 0 1 := by
        ext x
        constructor
        · rintro ⟨⟨s, hs, rfl⟩, hne⟩
          have hs0 : s ≠ 0 := fun h ↦ hne (congrArg f h)
          have hs1 : s ≠ 1 := fun h ↦ hne ((congrArg f h).trans f.endpoint)
          exact ⟨s, ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hs1⟩, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          refine ⟨⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩, ?_⟩
          exact fun h ↦ hs.1.ne' (f.injectiveOn ⟨hs.1.le, hs.2⟩ ht h)
      rw [him]
      exact isPreconnected_Ioo.image f (f.continuousOn.mono Ioo_subset_Icc_self)
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hinj : ∀ s ∈ Icc 0 1, f s = f t → s = t := by
        intro s hs heq
        rcases f.eq_or_endpoints hs (Ico_subset_Icc_self ht) heq with h | h | h
        · exact h
        · exact (ht.2.ne h.2).elim
        · exact (ht0 h.2).elim
      have him : f '' Icc 0 1 \ {f t} = f '' Ico 0 t ∪ f '' Ioc t 1 := by
        ext x
        constructor
        · rintro ⟨⟨s, hs, rfl⟩, hne⟩
          have hst : s ≠ t := fun h ↦ hne (congrArg f h)
          rcases lt_or_gt_of_ne hst with h | h
          · exact Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩
          · exact Or.inr ⟨s, ⟨h, hs.2⟩, rfl⟩
        · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
          · have hsI : s ∈ Icc 0 1 := ⟨hs.1, (hs.2.trans ht.2).le⟩
            exact ⟨⟨s, hsI, rfl⟩, fun h ↦ hs.2.ne (hinj s hsI h)⟩
          · have hsI : s ∈ Icc 0 1 := ⟨(htpos.trans hs.1).le, hs.2⟩
            exact ⟨⟨s, hsI, rfl⟩, fun h ↦ hs.1.ne' (hinj s hsI h)⟩
      rw [him]
      apply IsPreconnected.union (f 0)
      · exact ⟨0, ⟨le_rfl, htpos⟩, rfl⟩
      · exact ⟨1, ⟨ht.2, le_rfl⟩, f.endpoint⟩
      · exact isPreconnected_Ico.image f (f.continuousOn.mono
          (fun s hs ↦ ⟨hs.1, (hs.2.trans ht.2).le⟩))
      · exact isPreconnected_Ioc.image f (f.continuousOn.mono
          (fun s hs ↦ ⟨(htpos.trans hs.1).le, hs.2⟩))
  · rw [sdiff_singleton_eq_self hz]
    exact isPreconnected_Icc.image f f.continuousOn

theorem isPreconnected_punctured_jordan {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) (z : Schoenflies.Plane) :
    IsPreconnected (C \ {z}) := by
  obtain ⟨f, hf, rfl⟩ := hC
  let loop : SimpleLoop Schoenflies.Plane := ⟨f, hf.continuousOn, hf.closes.symm, hf.injOn⟩
  exact loop.isPreconnected_punctured z

end Reeken.Geometry
