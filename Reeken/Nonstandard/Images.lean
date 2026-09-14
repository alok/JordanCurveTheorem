import Reeken.Nonstandard.Shadow

/-!
# Internal images and passage back to standard curves

Image witnesses are obtained by the proved existential transfer rule. Compactness then
turns an internal intersection with an extended curve into a standard intersection
with the shadow of the internal set.
-/

open Filter

namespace Reeken.NSA

variable {ι α β : Type*} {U : Ultrafilter ι}

theorem map_mem_internalSet_image (f : α → β) (s : ι → Set α) {x : Star U α}
    (hx : x ∈ internalSet s) : map f x ∈ internalSet (fun i ↦ f '' s i) := by
  star_cases x
  exact hx.mono fun i hi ↦ ⟨x i, hi, rfl⟩

/-- Transfer of the witnesses in a set image. -/
theorem internalSet_image [Nonempty α] (f : α → β) (s : ι → Set α) :
    internalSet (U := U) (fun i ↦ f '' s i) = map f '' internalSet s := by
  change InternalSet.toSet (InternalSet.image (std f) (ofSeq s)) = _
  rw [InternalSet.coe_image, app_std_fun]
  rfl

variable [MetricSpace α] [MetricSpace β]

/-- A compactly parametrized standard curve that internally meets a set meets its shadow.
This is the standard-part argument for paths crossing the approximating polygon. -/
theorem compact_image_inter_shadow [Nonempty α] [Nonempty β]
    {s : Set α} (hs : IsCompact s) {f : α → β} (hf : ContinuousOn f s)
    {p : ℕ → Set β}
    (h : (starSet (U := hyperfilter ℕ) (f '' s) ∩ internalSet p).Nonempty) :
    (f '' s ∩ shadow p).Nonempty := by
  obtain ⟨y, hy, hp⟩ := h
  rw [starSet, internalSet_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨a, ha, hxa⟩ := compact_standard_part hs hx
  have hfa := hxa.map_compact hs hf hx ((std_mem_starSet s a).mpr ha)
  refine ⟨f a, ⟨a, ha, rfl⟩, map f x, hp, ?_⟩
  simpa only [map_std] using hfa

/-- Shadows commute with a continuous map when all the internal sets lie in one compact set. -/
theorem shadow_image [Nonempty α] [Nonempty β] {s : ℕ → Set α} {c : Set α}
    (hc : IsCompact c) (hsc : ∀ᶠ i in hyperfilter ℕ, s i ⊆ c)
    {f : α → β} (hf : ContinuousOn f c) :
    shadow (fun i ↦ f '' s i) = f '' shadow s := by
  ext b
  constructor
  · rintro ⟨y, hy, hyb⟩
    change y ∈ internalSet (fun i ↦ f '' s i) at hy
    rw [internalSet_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxc : x ∈ starSet c := (internalSet_subset s (fun _ ↦ c)).mpr hsc hx
    obtain ⟨a, ha, hxa⟩ := compact_standard_part hc hxc
    have hfa := hxa.map_compact hc hf hxc ((std_mem_starSet c a).mpr ha)
    refine ⟨a, ⟨x, hx, hxa⟩, ?_⟩
    exact standard_part_unique (by simpa only [map_std] using hfa) hyb
  · rintro ⟨a, ⟨x, hx, hxa⟩, rfl⟩
    have hxc : x ∈ starSet c := (internalSet_subset s (fun _ ↦ c)).mpr hsc hx
    have ha : a ∈ c := closed_standard_part hc.isClosed hxc hxa
    refine ⟨map f x, map_mem_internalSet_image f s hx, ?_⟩
    simpa only [map_std] using hxa.map_compact hc hf hxc ((std_mem_starSet c a).mpr ha)

end Reeken.NSA
