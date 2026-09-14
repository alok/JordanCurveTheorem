import Reeken.Nonstandard.Proximity

/-! # Appreciable separation from a common shadow on a compact set

This is the compactness/saturation step in Section 3: away from the common shadow
of the two polygon arcs, a point cannot be infinitesimally close to both arcs.
-/

open Filter Set Metric

namespace Reeken.NSA

variable {E : Type*} [MetricSpace E] [Nonempty E]

/-- A compact standard set avoiding two common shadows has one appreciable separation
bound for all internal points of both sets. -/
theorem InternalSet.compact_separation_from_common_shadow {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ atTop) {K : Set E} (hK : IsCompact K)
    {s t : InternalSet U E} (hdis : Disjoint K (s.shadow ∩ t.shadow)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ starSet K, ∀ y ∈ s, ∀ z ∈ t,
      std δ ≤ max (starDist y x) (starDist z x) := by
  let q : InternalSet U (E × E × E) := InternalSet.prod (std K) (s.prod t)
  let f : E × E × E → E × E := Prod.snd
  let g : E × E × E → E × E := fun w ↦ (w.1, w.1)
  have hn : ¬ ∃ w ∈ q, Near (app (std f) w) (app (std g) w) := by
    rintro ⟨w, hw, hnear⟩
    obtain ⟨x, yz, rfl⟩ := exists_pair w
    obtain ⟨y, z, rfl⟩ := exists_pair yz
    have hm := (InternalSet.pair_mem_prod _ _ _ _).mp hw
    have hym := (InternalSet.pair_mem_prod s t y z).mp hm.2
    have hxm : x ∈ starSet K := hm.1
    have hnyz : Near y x ∧ Near z x := by
      simpa only [f, g, app_std, map_snd_pair, map_diag, map_fst_pair,
        near_pair_iff] using hnear
    obtain ⟨a, ha, hxa⟩ := compact_standard_part hK hxm
    exact Set.disjoint_left.mp hdis ha
      ⟨⟨y, hym.1, hnyz.1.trans hxa⟩, ⟨z, hym.2, hnyz.2.trans hxa⟩⟩
  obtain ⟨δ, hδ, hd⟩ := (InternalSet.not_exists_near_iff hU q (std f) (std g)).mp hn
  refine ⟨δ, hδ, fun x hx y hy z hz ↦ ?_⟩
  have hw : pair x (pair y z) ∈ q :=
    (InternalSet.pair_mem_prod _ _ _ _).mpr
      ⟨hx, (InternalSet.pair_mem_prod s t y z).mpr ⟨hy, hz⟩⟩
  simpa only [f, g, app_std, map_snd_pair, map_diag, map_fst_pair, starDist_pair]
    using hd (pair x (pair y z)) hw

/-- Outside a common shadow, compactness makes the exclusion of simultaneous proximity uniform. -/
theorem compact_separation_from_common_shadow {K : Set E} (hK : IsCompact K)
    {s t : ℕ → Set E} (hdis : Disjoint K (shadow s ∩ shadow t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in hyperfilter ℕ,
      ∀ x ∈ K, ∀ y ∈ s i, ∀ z ∈ t i, δ ≤ max (dist y x) (dist z x) := by
  obtain ⟨δ, hδ, hd⟩ := InternalSet.compact_separation_from_common_shadow
    Nat.hyperfilter_le_atTop hK hdis
  refine ⟨δ, hδ, ?_⟩
  have h : ∀ w : Star (hyperfilter ℕ) (E × E × E),
      map Prod.fst w ∈ starSet K →
      map (fun a ↦ a.2.1) w ∈ (ofSeq s : InternalSet (hyperfilter ℕ) E) →
      map (fun a ↦ a.2.2) w ∈ (ofSeq t : InternalSet (hyperfilter ℕ) E) →
      std δ ≤ max (starDist (map (fun a ↦ a.2.1) w) (map Prod.fst w))
        (starDist (map (fun a ↦ a.2.2) w) (map Prod.fst w)) := by
    intro w hx hy hz
    exact hd _ hx _ hy _ hz
  star_transfer at h
  exact h.mono fun i hi x hx y hy z hz ↦ hi (x, y, z) hx hy hz

end Reeken.NSA
