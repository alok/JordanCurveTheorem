import Reeken.Geometry.ArcTopology
import Reeken.Nonstandard.PolygonRegularity
import Reeken.Nonstandard.Shadow

/-! # The two long arcs have only their endpoints in their common standard shadow

Parameter witnesses are extracted before taking standard parts. This is the
separation property needed on the square boundary in the published Section 3.
-/

open Filter Set Metric Topology
open Reeken.Geometry

namespace Reeken.NSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

omit [NormedSpace ℝ E] in
/-- A constrained near-curve point yields a parameter sequence with a standard part. -/
theorem exists_shadow_parameter {s : ℕ → Set E} {R : ℕ → ℝ → Prop} {d : ℕ → ℝ}
    (hd : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, d i < ε)
    (hs : ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ s i,
      ∃ t ∈ Icc 0 1, R i t ∧ dist x (f t) ≤ d i)
    {z : E} (hz : z ∈ shadow s) :
    ∃ t : ℕ → ℝ, ∃ a ∈ Icc (0 : ℝ) 1,
      (∀ᶠ i in hyperfilter ℕ, R i (t i)) ∧
      Near (ofSeq (U := hyperfilter ℕ) t) (std a) ∧ f a = z := by
  obtain ⟨x, hx, hxz⟩ := hz
  star_cases x
  have he : ∀ᶠ i in hyperfilter ℕ,
      ∃ t ∈ Icc 0 1, R i t ∧ dist (x i) (f t) ≤ d i := by
    filter_upwards [hs, hx] with i hi hxi
    exact hi _ hxi
  obtain ⟨t, ht⟩ := (exists_holds (U := hyperfilter ℕ)
    (fun i t ↦ t ∈ Icc 0 1 ∧ R i t ∧ dist (x i) (f t) ≤ d i)).mpr he
  star_cases t
  have htI : ofSeq (U := hyperfilter ℕ) t ∈ starSet (Icc (0 : ℝ) 1) :=
    ht.mono fun i hi ↦ hi.1
  obtain ⟨a, ha, hta⟩ := compact_standard_part isCompact_Icc htI
  have hxf : Near (ofSeq (U := hyperfilter ℕ) x) (ofSeq (fun i ↦ f (t i))) := by
    intro ε hε
    filter_upwards [ht, hd ε hε] with i hi hdi
    exact hi.2.2.trans_lt hdi
  have hfa : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ f (t i))) (std (f a)) := by
    simpa only [map_ofSeq, map_std] using hta.map_compact isCompact_Icc f.continuousOn
      htI ((std_mem_starSet _ _).mpr ha)
  exact ⟨t, a, ha, ht.mono fun i hi ↦ hi.2.1, hta,
    standard_part_unique (hxf.trans hfa) hxz⟩

variable (p : ℕ → InscribedPolygon f) (a b : (i : ℕ) → Fin ((p i).n + 1))

theorem shadow_forwardArc_subset
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i) {A B : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B)) :
    shadow (fun i ↦ (p i).forwardArc (a i) (b i)) ⊆ f '' (Icc 0 1 ∩ Icc A B) := by
  intro z hz
  obtain ⟨t, c, hc, ht, htc, hfc⟩ := exists_shadow_parameter hmax
    (hab.mono fun i hi x hx ↦ (p i).exists_forwardArc_parameter (a i) (b i) hi hx) hz
  have hta := (near_std_iff_tendsto _ _).mp ha
  have htb := (near_std_iff_tendsto _ _).mp hb
  have htt := (near_std_iff_tendsto _ _).mp htc
  exact ⟨c, ⟨hc, le_of_tendsto_of_tendsto hta htt (ht.mono fun i hi ↦ hi.1),
    le_of_tendsto_of_tendsto htt htb (ht.mono fun i hi ↦ hi.2)⟩, hfc⟩

theorem shadow_backwardArc_subset
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε) {A B : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B)) :
    shadow (fun i ↦ (p i).backwardArc (a i) (b i)) ⊆
      f '' (Icc 0 1 ∩ (Iic A ∪ Ici B)) := by
  intro z hz
  obtain ⟨t, c, hc, ht, htc, hfc⟩ := exists_shadow_parameter hmax
    (Eventually.of_forall fun i x hx ↦ (p i).exists_backwardArc_parameter (a i) (b i) hx) hz
  have hta := (near_std_iff_tendsto _ _).mp ha
  have htb := (near_std_iff_tendsto _ _).mp hb
  have htt := (near_std_iff_tendsto _ _).mp htc
  refine ⟨c, ⟨hc, ?_⟩, hfc⟩
  rcases Ultrafilter.eventually_or.mp ht with ht | ht
  · exact Or.inl (le_of_tendsto_of_tendsto htt hta ht)
  · exact Or.inr (le_of_tendsto_of_tendsto htb htt ht)

/-- The common shadow of the two long polygon arcs contains only the limiting cut points. -/
theorem common_arc_shadow_subset
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i) {A B : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B)) :
    shadow (fun i ↦ (p i).forwardArc (a i) (b i)) ∩
      shadow (fun i ↦ (p i).backwardArc (a i) (b i)) ⊆ {f A, f B} := by
  have hA : A ∈ Icc (0 : ℝ) 1 := closed_standard_part isClosed_Icc
    (x := ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i)))
    (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem (a i))) ha
  have hB : B ∈ Icc (0 : ℝ) 1 := closed_standard_part isClosed_Icc
    (x := ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i)))
    (Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem (b i))) hb
  rintro z ⟨hzF, hzB⟩
  obtain ⟨u, hu, rfl⟩ := shadow_forwardArc_subset p a b hmax hab ha hb hzF
  obtain ⟨v, hv, hvu⟩ := shadow_backwardArc_subset p a b hmax ha hb hzB
  rcases f.eq_or_endpoints hu.1 hv.1 hvu.symm with huv | ⟨hu0, hv1⟩ | ⟨hu1, hv0⟩
  · subst v
    rcases hv.2 with hv | hv
    · exact Or.inl (congrArg f (le_antisymm hv hu.2.1))
    · exact Or.inr (congrArg f (le_antisymm hu.2.2 hv))
  · have huA : u = A := le_antisymm (by rw [hu0]; exact hA.1) hu.2.1
    exact Or.inl (congrArg f huA)
  · have huB : u = B := le_antisymm hu.2.2 (by rw [hu1]; exact hB.2)
    exact Or.inr (congrArg f huB)

end Reeken.NSA
