import Reeken.Geometry.LoopPuncture

/-! # A closed curve cannot pass through a free endpoint of an attached arc

Near the endpoint, a short initial subarc avoids the other closed set. Removing
an interior point of that subarc would disconnect any closed curve passing through
the endpoint. This is the endpoint argument needed to make the clipped cell meet
both original polygon arcs.
-/

open Set Metric Schoenflies

namespace Reeken.Geometry

theorem exists_ne_on_jordan {Q : Set Plane} (hQ : IsJordanCurve Q) (a : Plane) :
    ∃ y ∈ Q, y ≠ a := by
  obtain ⟨g, hg, rfl⟩ := hQ
  have hne : g 0 ≠ g (1 / 2) := by
    intro he
    have := hg.injOn (by norm_num) (by norm_num) he
    norm_num at this
  by_cases ha : g 0 = a
  · exact ⟨g (1 / 2), ⟨1 / 2, by norm_num, rfl⟩, fun he ↦ hne (ha.trans he.symm)⟩
  · exact ⟨g 0, ⟨0, zero_mem_I, rfl⟩, ha⟩

/-- An endpoint outside the attached closed set cannot belong to a Jordan curve
carried by the arc and that set. -/
theorem not_subset_arc_union_of_endpoint {Q A S : Set Plane} {a b : Plane}
    (hQ : IsJordanCurve Q) (hA : IsArcBetween A a b) (hS : IsClosed S)
    (haQ : a ∈ Q) (haS : a ∉ S) : ¬ Q ⊆ A ∪ S := by
  intro hsub
  obtain ⟨y, hyQ, hya⟩ := exists_ne_on_jordan hQ a
  obtain ⟨g, hg, hginj, him, hg0, _⟩ := hA
  have haO : a ∈ Sᶜ ∩ ({y} : Set Plane)ᶜ := ⟨haS, Ne.symm hya⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (hS.isOpen_compl.inter isClosed_singleton.isOpen_compl) a haO
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp (hg 0 zero_mem_I) ε hε
  let s := min (δ / 2) (1 / 2)
  have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
  have hsδ : s < δ := (min_le_left _ _).trans_lt (by linarith)
  have hs1 : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hprefix : ∀ t ∈ Icc 0 s, g t ∈ Sᶜ ∩ ({y} : Set Plane)ᶜ := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, ← hg0]
    apply hnear ⟨ht.1, ht.2.trans hs1.le⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hsδ
  let X := g '' Icc 0 s
  let Y := g '' Icc s 1 ∪ S
  have hX : IsClosed X := (isCompact_Icc.image_of_continuousOn
    (hg.mono (fun t ht ↦ ⟨ht.1, ht.2.trans hs1.le⟩))).isClosed
  have hY : IsClosed Y := (isCompact_Icc.image_of_continuousOn
    (hg.mono (fun t ht ↦ ⟨hs0.le.trans ht.1, ht.2⟩))).isClosed.union hS
  have hcover : Q ⊆ X ∪ Y := by
    intro x hx
    rcases hsub hx with hxA | hxS
    · rw [← him] at hxA
      obtain ⟨t, ht, rfl⟩ := hxA
      rcases le_total t s with hts | hst
      · exact Or.inl ⟨t, ⟨ht.1, hts⟩, rfl⟩
      · exact Or.inr (Or.inl ⟨t, ⟨hst, ht.2⟩, rfl⟩)
    · exact Or.inr (Or.inr hxS)
  have hinter : X ∩ Y ⊆ {g s} := by
    rintro x ⟨⟨u, hu, rfl⟩, hxY⟩
    rcases hxY with ⟨v, hv, he⟩ | hxS
    · have huv := hginj ⟨hs0.le.trans hv.1, hv.2⟩ ⟨hu.1, hu.2.trans hs1.le⟩ he
      have hus : u = s := le_antisymm hu.2 (huv ▸ hv.1)
      exact congrArg g hus
    · exact ((hprefix u hu).1 hxS).elim
  have haY : a ∉ Y := by
    rintro (⟨t, ht, he⟩ | haS')
    · have ht0 := hginj ⟨hs0.le.trans ht.1, ht.2⟩ zero_mem_I (he.trans hg0.symm)
      exact hs0.not_ge (ht0 ▸ ht.1)
    · exact haS haS'
  have hyX : y ∉ X := by
    rintro ⟨t, ht, he⟩
    exact (hprefix t ht).2 he
  have hgsX : g s ∈ X := ⟨s, ⟨hs0.le, le_rfl⟩, rfl⟩
  have hgsY : g s ∈ Y := Or.inl ⟨s, ⟨le_rfl, hs1.le⟩, rfl⟩
  have ha' : a ∈ Q \ {g s} := ⟨haQ, fun he ↦ haY (he ▸ hgsY)⟩
  have hy' : y ∈ Q \ {g s} := ⟨hyQ, fun he ↦ hyX (he ▸ hgsX)⟩
  have hsep : (Q \ {g s}) ∩ (X ∩ Y) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun _ hx ↦ hx.1.2 (hinter hx.2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_punctured_jordan hQ (g s)) X Y hX hY
      (sdiff_subset.trans hcover) hsep with h | h
  · exact hyX (h hy')
  · exact haY (h ha')

end Reeken.Geometry
