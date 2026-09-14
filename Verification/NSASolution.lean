import Reeken

open Filter Topology

namespace Verification

universe u v w

theorem compact_standard_part {ι : Type u} {α : Type v} [MetricSpace α]
    (U : Ultrafilter ι) (s : Set α) (hs : IsCompact s) (x : ι → α)
    (hx : ∀ᶠ i in U, x i ∈ s) :
    ∃ a ∈ s, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, dist (x i) a < ε :=
  Reeken.NSA.compact_standard_part (U := U) hs (x := Reeken.NSA.ofSeq x) hx

theorem countable_saturation {α : Type u} [Nonempty α] (P : ℕ → ℕ → α → Prop)
    (h : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ a, ∀ k ≤ n, P k i a) :
    ∃ x : ℕ → α, ∀ k, ∀ᶠ i in hyperfilter ℕ, P k i (x i) := by
  obtain ⟨x, hx⟩ := Reeken.NSA.countable_saturation_of_eventually P h
  obtain ⟨x, rfl⟩ := Reeken.NSA.ofSeq_surjective x
  exact ⟨x, hx⟩

theorem compact_injective_reflects_near {ι : Type u} {α : Type v} {β : Type w}
    [MetricSpace α] [MetricSpace β] (U : Ultrafilter ι) (s : Set α) (hs : IsCompact s)
    (f : α → β) (hf : ContinuousOn f s) (hinj : Set.InjOn f s) (x y : ι → α)
    (hx : ∀ᶠ i in U, x i ∈ s) (hy : ∀ᶠ i in U, y i ∈ s)
    (hxy : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, dist (f (x i)) (f (y i)) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, dist (x i) (y i) < ε :=
  Reeken.NSA.compact_injective_reflects_near (U := U) hs hf hinj
    (x := Reeken.NSA.ofSeq x) (y := Reeken.NSA.ofSeq y) hx hy hxy

end Verification
