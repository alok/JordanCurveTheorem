import Reeken.Geometry.ArcParametrization
import Reeken.Geometry.SmallerRadius

/-! # A fixed finite choice between the two polygon arcs

The selected edge list joins the prescribed vertices and is contained in the
polygon. Choosing the arc with smaller radius makes it infinitesimal whenever
the two endpoints are near, by Lemma 1(iii).
-/

open Set Metric Schoenflies

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem toPrePolygon_vertex_natCast (hn : 2 ≤ p.n) (hp : p.Simple) (a : Fin (p.n + 1)) :
    (p.toPrePolygon hn hp).vertex (a.val : ZMod (p.n - 2 + 3)) = p.vertex a := by
  change p.vertex (p.cyclicIndex hn (a.val : ZMod (p.n - 2 + 3))) = _
  rw [p.cyclicIndex_natCast]

theorem toPrePolygon_backwardArc (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a < b) :
    (p.toPrePolygon hn hp).arc (b.val : ZMod (p.n - 2 + 3)) (p.n + 1 - (b.val - a.val)) =
      p.backwardArc a b := by
  let P := p.toPrePolygon hn hp
  let A : ZMod (p.n - 2 + 3) := a.val
  let k := b.val - a.val
  have hcast : A + k = (b.val : ZMod (p.n - 2 + 3)) := by
    change (a.val : ZMod (p.n - 2 + 3)) + (b.val - a.val : ℕ) = _
    rw [← Nat.cast_add, Nat.add_sub_of_le (show a.val ≤ b.val from hab.le)]
  have hF : P.arc A k = p.forwardArc a b := p.toPrePolygon_forwardArc hn hp hab
  have hU : p.forwardArc a b ∪ P.arc (b.val : ZMod (p.n - 2 + 3))
      (p.n + 1 - k) = p.trace := by
    rw [← hF, ← hcast, show p.n + 1 = p.n - 2 + 3 by omega, P.arc_union A (by dsimp [k]; omega),
      p.toPrePolygon_carrier]
  have hI : p.forwardArc a b ∩ P.arc (b.val : ZMod (p.n - 2 + 3))
      (p.n + 1 - k) = {p.vertex a, p.vertex b} := by
    rw [← hF, ← hcast, show p.n + 1 = p.n - 2 + 3 by omega,
      P.arc_inter A (by dsimp [k]; omega) (by dsimp [k]; have := b.isLt; omega), hcast]
    rw [p.toPrePolygon_vertex_natCast, p.toPrePolygon_vertex_natCast]
  ext x
  have hu := congrArg (fun s : Set Plane ↦ x ∈ s) (hU.trans (p.arcs_union a b).symm)
  have hi := congrArg (fun s : Set Plane ↦ x ∈ s) (hI.trans (hp.arcs_inter hab.le).symm)
  simp only [mem_union, mem_inter_iff] at hu hi
  by_cases hx : x ∈ p.forwardArc a b
  · simpa only [hx, true_and] using Iff.of_eq hi
  · simpa only [hx, false_or] using Iff.of_eq hu

noncomputable def forwardPieces (hn : 2 ≤ p.n) (hp : p.Simple) (a b : Fin (p.n + 1)) : List Piece :=
  (p.toPrePolygon hn hp).arcPieces a.val (b.val - a.val)

noncomputable def backwardPieces (hn : 2 ≤ p.n) (hp : p.Simple) (a b : Fin (p.n + 1)) : List Piece :=
  (p.toPrePolygon hn hp).arcPieces b.val (p.n + 1 - (b.val - a.val))

theorem forwardPieces_chain (hn : 2 ≤ p.n) (hp : p.Simple) {a b : Fin (p.n + 1)} (hab : a ≤ b) :
    IsChainFrom (p.forwardPieces hn hp a b) (p.vertex a) (p.vertex b) := by
  have h := (p.toPrePolygon hn hp).isChainFrom_arcPieces a.val (b.val - a.val)
  have he : (a.val : ZMod (p.n - 2 + 3)) + (b.val - a.val : ℕ) = b.val := by
    rw [← Nat.cast_add, Nat.add_sub_of_le (show a.val ≤ b.val from hab)]
  rwa [he, p.toPrePolygon_vertex_natCast, p.toPrePolygon_vertex_natCast] at h

theorem backwardPieces_chain (hn : 2 ≤ p.n) (hp : p.Simple) {a b : Fin (p.n + 1)} (hab : a ≤ b) :
    IsChainFrom (p.backwardPieces hn hp a b) (p.vertex a) (p.vertex b) := by
  have h := (p.toPrePolygon hn hp).isChainFrom_arcPieces b.val (p.n + 1 - (b.val - a.val))
  have he : (b.val : ZMod (p.n - 2 + 3)) + (p.n + 1 - (b.val - a.val) : ℕ) = a.val := by
    rw [← Nat.cast_add]
    have hn' : b.val + (p.n + 1 - (b.val - a.val)) = a.val + (p.n - 2 + 3) := by
      have := b.isLt
      have : a.val ≤ b.val := hab
      omega
    rw [hn', Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [he, p.toPrePolygon_vertex_natCast, p.toPrePolygon_vertex_natCast] at h
  exact fun g ↦ (h g).trans (add_comm _ _)

theorem forwardPieces_subset_arc (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) : cover (p.forwardPieces hn hp a b) ⊆ p.forwardArc a b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [forwardPieces]
  · exact (p.toPrePolygon_forwardArc hn hp hlt).subset

theorem backwardPieces_subset_arc (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) : cover (p.backwardPieces hn hp a b) ⊆ p.backwardArc a b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have he : p.backwardArc a a = p.trace := by
      ext x
      simp only [backwardArc, trace, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro (rfl | ⟨i, _, hx⟩)
        · exact ⟨a, left_mem_segment ℝ _ _⟩
        · exact ⟨i, hx⟩
      · rintro ⟨i, hx⟩
        exact Or.inr ⟨i, lt_or_ge i a, hx⟩
    rw [he, ← p.toPrePolygon_carrier hn hp]
    exact (p.toPrePolygon hn hp).arc_subset_carrier _ _
  · exact (p.toPrePolygon_backwardArc hn hp hlt).subset

noncomputable def orderedSmallArcPieces (hn : 2 ≤ p.n) (hp : p.Simple)
    (a b : Fin (p.n + 1)) : List Piece :=
  smallerRadiusPieces (p.vertex a) (p.forwardPieces hn hp a b) (p.backwardPieces hn hp a b)

theorem orderedSmallArcPieces_chain (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) :
    IsChainFrom (p.orderedSmallArcPieces hn hp a b) (p.vertex a) (p.vertex b) := by
  classical
  unfold orderedSmallArcPieces smallerRadiusPieces
  split_ifs
  · exact p.forwardPieces_chain hn hp hab
  · exact p.backwardPieces_chain hn hp hab

theorem orderedSmallArcPieces_subset_ball (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) {r : ℝ}
    (h : p.forwardArc a b ⊆ ball (p.vertex a) r ∨ p.backwardArc a b ⊆ ball (p.vertex a) r) :
    cover (p.orderedSmallArcPieces hn hp a b) ⊆ ball (p.vertex a) r := by
  rw [orderedSmallArcPieces, cover_smallerRadiusPieces]
  rcases h with h | h
  · exact smallerRadiusSet_subset_ball_of_left ((p.forwardPieces_subset_arc hn hp hab).trans h)
  · exact smallerRadiusSet_subset_ball_of_right ((p.backwardPieces_subset_arc hn hp hab).trans h)

theorem orderedSmallArcPieces_subset_trace (hn : 2 ≤ p.n) (hp : p.Simple)
    (a b : Fin (p.n + 1)) : cover (p.orderedSmallArcPieces hn hp a b) ⊆ p.trace := by
  classical
  unfold orderedSmallArcPieces smallerRadiusPieces
  split_ifs
  · exact ((p.toPrePolygon hn hp).arc_subset_carrier _ _).trans
      (p.toPrePolygon_carrier hn hp).subset
  · exact ((p.toPrePolygon hn hp).arc_subset_carrier _ _).trans
      (p.toPrePolygon_carrier hn hp).subset

open scoped Classical in
noncomputable def chosenArcPieces (a b : Fin (p.n + 1)) : List Piece :=
  if h : 2 ≤ p.n ∧ p.Simple then
    if a ≤ b then p.orderedSmallArcPieces h.1 h.2 a b else p.orderedSmallArcPieces h.1 h.2 b a
  else []

theorem chosenArcPieces_chain (hn : 2 ≤ p.n) (hp : p.Simple) (a b : Fin (p.n + 1)) :
    IsChainFrom (p.chosenArcPieces a b) (p.vertex a) (p.vertex b) := by
  classical
  rw [chosenArcPieces, dif_pos ⟨hn, hp⟩]
  split_ifs with hab
  · exact p.orderedSmallArcPieces_chain hn hp hab
  · have h := p.orderedSmallArcPieces_chain hn hp (le_of_not_ge hab)
    exact fun g ↦ (h g).trans (add_comm _ _)

theorem chosenArcPieces_subset_trace (a b : Fin (p.n + 1)) :
    cover (p.chosenArcPieces a b) ⊆ p.trace := by
  classical
  unfold chosenArcPieces
  split_ifs with h hab
  · exact p.orderedSmallArcPieces_subset_trace h.1 h.2 a b
  · exact p.orderedSmallArcPieces_subset_trace h.1 h.2 b a
  · simp

theorem chosenArcPieces_symm (a b : Fin (p.n + 1)) : p.chosenArcPieces a b = p.chosenArcPieces b a := by
  classical
  by_cases h : 2 ≤ p.n ∧ p.Simple
  · simp only [chosenArcPieces, dif_pos h]
    by_cases hab : a ≤ b
    · by_cases hba : b ≤ a
      · have he := le_antisymm hab hba
        subst b
        rfl
      · simp only [if_pos hab, if_neg hba]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [if_neg hab, if_pos hba]
  · simp only [chosenArcPieces, dif_neg h]

end Reeken.Geometry.InscribedPolygon
