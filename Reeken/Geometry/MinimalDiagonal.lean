import Reeken.Geometry.DiagonalCut

/-! # A minimal-span internal diagonal cuts off a triangle

Among internal diagonals, minimize the number of consecutive boundary edges
spanned. If there were more than two, the cut-off polygon would have its own
internal diagonal, spanning fewer old edges. Hence some internal diagonal spans
exactly two edges, including for presentations with collinear vertices.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem exists_two_edge_internal_diagonal {m : ℕ} (P : PrePolygon m) (hm : 0 < m) :
    ∃ a : ZMod (m + 3),
      openSegment ℝ (P.vertex a) (P.vertex (a + 2)) ⊆ inside P.carrier := by
  classical
  let D : ℕ → Prop := fun k ↦ 2 ≤ k ∧ k ≤ m + 1 ∧ ∃ a : ZMod (m + 3),
    openSegment ℝ (P.vertex a) (P.vertex (a + (k : ZMod (m + 3)))) ⊆ inside P.carrier
  have hex : ∃ k, D k := by
    obtain ⟨p, q, hq, hlo, hhi, hseg⟩ := exists_ordered_internal_diagonal P hm
    refine ⟨q - p, hlo, hhi, (p : ZMod (m + 3)), ?_⟩
    rw [Nat.cast_sub (by omega : p ≤ q), add_sub_cancel]
    exact hseg
  let k := Nat.find hex
  have hk : D k := Nat.find_spec hex
  have hmin : ∀ d, D d → k ≤ d := fun d hd ↦ Nat.find_min' hex hd
  obtain ⟨hklo, hkhi, a, hseg⟩ := hk
  obtain ⟨l, hl⟩ : ∃ l : ℕ, k = l + 2 := ⟨k - 2, by omega⟩
  have hlen : l + 2 ≤ m + 1 := by omega
  have hsegL : openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ))) ⊆ inside P.carrier := by
    simpa only [hl] using hseg
  have hdiag : Disjoint (openSegment ℝ (P.vertex a) (P.vertex (a + (l + 2 : ℕ)))) P.carrier :=
    disjoint_left.mpr fun _ hx hxP ↦ (hsegL hx).1 hxP
  let Q := closeArc P a l hlen hdiag
  have hinside : inside Q.carrier ⊆ inside P.carrier := closeArc_inside_subset P a l hlen hdiag hsegL
  have hlzero : l = 0 := by
    by_contra hlne
    obtain ⟨p, q, hq, hlo, hhi, hcutQ⟩ := exists_ordered_internal_diagonal Q (Nat.pos_of_ne_zero hlne)
    have hp : p < l + 3 := by omega
    have hcut : openSegment ℝ (P.vertex (a + (p : ZMod (m + 3))))
        (P.vertex (a + (q : ZMod (m + 3)))) ⊆ inside P.carrier := by
      have ht := hcutQ.trans hinside
      change openSegment ℝ (P.vertex (arcIndex a (p : ZMod (l + 3))))
        (P.vertex (arcIndex a (q : ZMod (l + 3)))) ⊆ inside P.carrier at ht
      simpa only [arcIndex, ZMod.val_cast_of_lt hp, ZMod.val_cast_of_lt hq] using ht
    have hd : D (q - p) := by
      refine ⟨hlo, by omega, a + (p : ZMod (m + 3)), ?_⟩
      rw [Nat.cast_sub (by omega : p ≤ q), show a + (p : ZMod (m + 3)) +
        ((q : ZMod (m + 3)) - p) = a + q by ring]
      exact hcut
    have := hmin (q - p) hd
    omega
  refine ⟨a, ?_⟩
  simpa only [hl, hlzero, Nat.zero_add, Nat.cast_ofNat] using hseg

end Reeken.Geometry
