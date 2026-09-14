import Reeken.Nonstandard.SimpleApproximation

open Filter Set

namespace Verification

universe u

/-- An independent sequence statement of Reeken's simple inscribed approximation.
All parameter conditions, segments, intersections, and shadow estimates are explicit. -/
theorem simple_inscribed_approximation {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 1)) (hend : f 1 = f 0)
    (hinj : Set.InjOn f (Ico 0 1)) :
    ∃ n : ℕ → ℕ, ∃ t : (i : ℕ) → Fin (n i + 1) → ℝ,
      (∀ i, (∀ j, t i j ∈ Ico 0 1) ∧ StrictMono (t i) ∧
        (∀ j : Fin (n i), t i j.succ - t i j.castSucc ≤ 1 / 2) ∧
        1 / 2 ≤ t i (Fin.last (n i)) - t i 0) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, ∀ j,
        dist (f (t i j)) (f (t i (Fin.lastCases 0 Fin.succ j))) < ε) ∧
      (∀ᶠ i in hyperfilter ℕ, ∀ a b : Fin (n i + 1), a ≠ b → ∀ x,
        x ∈ segment ℝ (f (t i a)) (f (t i (Fin.lastCases 0 Fin.succ a))) →
        x ∈ segment ℝ (f (t i b)) (f (t i (Fin.lastCases 0 Fin.succ b))) →
        (Fin.lastCases 0 Fin.succ a = b ∧ x = f (t i b)) ∨
        (Fin.lastCases 0 Fin.succ b = a ∧ x = f (t i a))) ∧
      ∀ z : E, (∃ x : ℕ → E,
        (∀ᶠ i in hyperfilter ℕ, x i ∈ ⋃ j : Fin (n i + 1),
          segment ℝ (f (t i j)) (f (t i (Fin.lastCases 0 Fin.succ j)))) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, dist (x i) z < ε) ↔
        z ∈ f '' Icc 0 1 := by
  let loop : Reeken.Geometry.SimpleLoop E := ⟨f, hf, hend, hinj⟩
  obtain ⟨p, hmax, hs, hshadow⟩ := Reeken.NSA.exists_simple_polygon loop
  refine ⟨fun i ↦ (p i).n, fun i ↦ (p i).time, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ ⟨(p i).time_mem, (p i).increasing, (p i).forward_half, (p i).span_half⟩
  · intro ε hε
    filter_upwards [hmax ε hε] with i hi j
    exact ((p i).edgeLength_le_maxEdge j).trans_lt hi
  · filter_upwards [hs] with i hi a b hab x hxa hxb
    exact hi.2 a b hab x ⟨hxa, hxb⟩
  · intro z
    change _ ↔ z ∈ loop '' Icc 0 1
    rw [← hshadow]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨Reeken.NSA.ofSeq x, hx, hz⟩
    · rintro ⟨x, hx, hz⟩
      obtain ⟨x, rfl⟩ := Reeken.NSA.ofSeq_surjective x
      exact ⟨x, hx, hz⟩

end Verification
