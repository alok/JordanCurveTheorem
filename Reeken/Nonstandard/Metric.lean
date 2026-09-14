import Reeken.Nonstandard.InternalSet
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-!
# Infinitesimal closeness in metric spaces

Compactness produces standard parts without an added standard-part axiom. A compact
embedding both preserves and reflects infinitesimal closeness, as used in Reeken's Lemma 1.
-/

open Filter Topology

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι}

/-- Two internal points are close at every positive standard metric scale. -/
def Near [PseudoMetricSpace α] (x y : Star U α) : Prop :=
  ∀ ε : ℝ, 0 < ε → Germ.LiftRel (fun a b ↦ dist a b < ε) x y

variable [PseudoMetricSpace α]

@[simp] theorem near_ofSeq (x y : ι → α) :
    Near (ofSeq (U := U) x) (ofSeq y) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, dist (x i) (y i) < ε := Iff.rfl

theorem Near.refl (x : Star U α) : Near x x := by
  star_cases x
  intro ε hε
  exact Eventually.of_forall fun i ↦ by simpa using hε

theorem Near.symm {x y : Star U α} (h : Near x y) : Near y x := by
  star_cases x y
  intro ε hε
  exact (h ε hε).mono fun i hi ↦ by simpa only [dist_comm] using hi

theorem Near.trans {x y z : Star U α} (hxy : Near x y) (hyz : Near y z) : Near x z := by
  star_cases x y z
  intro ε hε
  filter_upwards [hxy (ε / 2) (half_pos hε), hyz (ε / 2) (half_pos hε)] with i hi hj
  have ht := dist_triangle (x i) (y i) (z i)
  linarith

theorem near_std_iff_tendsto (x : ι → α) (a : α) :
    Near (ofSeq (U := U) x) (std a) ↔ Tendsto x (U : Filter ι) (𝓝 a) :=
  Metric.tendsto_nhds.symm

/-- An internal point in the extension of a compact set has a standard part in that set. -/
theorem compact_standard_part {s : Set α} (hs : IsCompact s) {x : Star U α}
    (hx : x ∈ starSet s) : ∃ a ∈ s, Near x (std a) := by
  star_cases x
  obtain ⟨a, ha, hlim⟩ := hs.ultrafilter_le_nhds' (Ultrafilter.map x U) hx
  exact ⟨a, ha, (near_std_iff_tendsto x a).mpr hlim⟩

/-- A closed set contains the standard part of any internal point in its extension. -/
theorem closed_standard_part {s : Set α} (hs : IsClosed s) {x : Star U α} {a : α}
    (hx : x ∈ starSet s) (ha : Near x (std a)) : a ∈ s := by
  star_cases x
  exact hs.mem_of_tendsto ((near_std_iff_tendsto x a).mp ha) hx

variable [PseudoMetricSpace β]

theorem Near.map_uniformContinuous {f : α → β} (hf : UniformContinuous f)
    {x y : Star U α} (hxy : Near x y) : Near (map f x) (map f y) := by
  star_cases x y
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  exact (hxy δ hδ).mono fun i hi ↦ hd hi

theorem Near.map_uniformContinuousOn {f : α → β} {s : Set α}
    (hf : UniformContinuousOn f s) {x y : Star U α}
    (hx : x ∈ starSet s) (hy : y ∈ starSet s) (hxy : Near x y) :
    Near (map f x) (map f y) := by
  star_cases x y
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hf ε hε
  filter_upwards [hx, hy, hxy δ hδ] with i hxi hyi hi
  exact hd (x i) hxi (y i) hyi hi

/-- Continuity on a compact set preserves infinitesimal closeness everywhere on its extension. -/
theorem Near.map_compact {s : Set α} (hs : IsCompact s) {f : α → β}
    (hf : ContinuousOn f s) {x y : Star U α}
    (hx : x ∈ starSet s) (hy : y ∈ starSet s) (hxy : Near x y) :
    Near (map f x) (map f y) :=
  hxy.map_uniformContinuousOn (hs.uniformContinuousOn_of_continuous hf) hx hy

end Reeken.NSA

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι} [MetricSpace α] [MetricSpace β]

@[simp] theorem near_std_std {a b : α} : Near (std a : Star U α) (std b) ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have hd : 0 < dist a b := dist_pos.mpr hab
    have hh : dist a b < dist a b := Filter.eventually_const.mp (h (dist a b) hd)
    exact lt_irrefl _ hh
  · rintro rfl
    exact Near.refl _

theorem standard_part_unique {x : Star U α} {a b : α}
    (ha : Near x (std a)) (hb : Near x (std b)) : a = b :=
  near_std_std.mp (ha.symm.trans hb)

/-- The inverse-continuity step used at the beginning of the Kanovei–Reeken argument. -/
theorem compact_injective_reflects_near {s : Set α} (hs : IsCompact s) {f : α → β}
    (hf : ContinuousOn f s) (hinj : Set.InjOn f s) {x y : Star U α}
    (hx : x ∈ starSet s) (hy : y ∈ starSet s)
    (hxy : Near (map f x) (map f y)) : Near x y := by
  obtain ⟨a, ha, hxa⟩ := compact_standard_part hs hx
  obtain ⟨b, hb, hyb⟩ := compact_standard_part hs hy
  have hfa := hxa.map_compact hs hf hx ((std_mem_starSet _ _).mpr ha)
  have hfb := hyb.map_compact hs hf hy ((std_mem_starSet _ _).mpr hb)
  have hab : f a = f b := by
    simpa only [map_std, near_std_std] using hfa.symm.trans (hxy.trans hfb)
  have hab' := hinj ha hb hab
  subst b
  exact hxa.trans hyb.symm

theorem compact_injective_near_iff {s : Set α} (hs : IsCompact s) {f : α → β}
    (hf : ContinuousOn f s) (hinj : Set.InjOn f s) {x y : Star U α}
    (hx : x ∈ starSet s) (hy : y ∈ starSet s) :
    Near (map f x) (map f y) ↔ Near x y :=
  ⟨compact_injective_reflects_near hs hf hinj hx hy, fun h ↦ h.map_compact hs hf hx hy⟩

end Reeken.NSA
