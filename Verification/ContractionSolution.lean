import Reeken.Geometry.ConvexAttachment
import Reeken.Geometry.TriangleContraction

open Set

namespace Verification

theorem triangle_contraction (a b c : EuclideanSpace ℝ (Fin 2))
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    let C := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
    let U := {x | x ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ x)}
    ContractibleSpace (closure U) ∧ IsSimplyConnected U := by
  let P := Schoenflies.triangle (a := a) (b := b) (c := c) h
  have he : P.carrier = segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
    ext x
    change (x ∈ ⋃ i, P.edge i) ↔ _
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have hc : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      rcases hc i with rfl | rfl | rfl
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hx | hx) | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
      · exact ⟨2, hx⟩
  change ContractibleSpace (closure (Schoenflies.inside _)) ∧ IsSimplyConnected (Schoenflies.inside _)
  rw [← he]
  exact ⟨Reeken.Geometry.contractibleSpace_triangle_closed_inside P,
    Reeken.Geometry.isSimplyConnected_triangle_inside P⟩

theorem convex_attachment_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E) (hA : IsClosed A) (hB : IsClosed B) (hconv : Convex ℝ A)
    (a b : E) (hinter : A ∩ B = segment ℝ a b) [ContractibleSpace B] :
    ContractibleSpace (A ∪ B : Set E) :=
  Reeken.Geometry.contractibleSpace_union_of_segment_inter hA hB hconv a b hinter

end Verification
