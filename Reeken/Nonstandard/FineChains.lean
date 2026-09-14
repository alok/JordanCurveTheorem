import Reeken.Geometry.FineChains
import Reeken.Nonstandard.Monads

/-! # Internal fine subdivisions of an arbitrary polygon family -/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

theorem exists_internal_fine_chain (q : ℕ → Σ m, ClosedPolygon m) :
    ∃ L : ℕ → List Piece,
      (∀ i, cover (L i) = (q i).2.carrier ∧ IsClosedChain (L i) ∧
        (∀ P ∈ L i, P.Nondeg) ∧
        ∀ u : Plane, (∀ P ∈ (q i).2.pieces, hgt u P.1 ≠ hgt u P.2) →
          ∀ x, parity u (L i) x = parity u (q i).2.pieces x) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i, dist P.1 P.2 < η := by
  have hex (i : ℕ) := exists_fine_chain (q i).2.pieces (q i).2.isClosedChain_pieces
    (q i).2.pieces_nondeg (ε := 1 / (i + 1 : ℝ)) (by positivity)
  choose L hL using hex
  refine ⟨L, fun i ↦ ⟨(hL i).1.trans (q i).2.cover_pieces, (hL i).2.1,
    (hL i).2.2.1, (hL i).2.2.2.2⟩, ?_⟩
  intro η hη
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  filter_upwards [Nat.hyperfilter_le_atTop (eventually_ge_atTop N)] with i hi
  intro P hP
  exact ((hL i).2.2.2.1 P hP).trans
    ((one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hi 1)).trans_lt hN)

end Reeken.NSA
