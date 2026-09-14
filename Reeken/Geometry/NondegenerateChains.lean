import Schoenflies.ParitySplitting

/-! # Removing zero-length edges from crossing-count calculations

A repeated endpoint contributes zero to both the chain boundary and crossing
parity. Removing such pieces allows one generic ray direction to be chosen even
when a nearest connection is degenerate.
-/

open Schoenflies

namespace Reeken.Geometry

noncomputable def nondegeneratePieces (L : List Piece) : List Piece := by
  classical
  exact L.filter (fun P ↦ decide P.Nondeg)

theorem mem_nondegeneratePieces {L : List Piece} {P : Piece} :
    P ∈ nondegeneratePieces L ↔ P ∈ L ∧ P.Nondeg := by
  classical
  simp [nondegeneratePieces]

theorem nondegeneratePieces_nondeg (L : List Piece) :
    ∀ P ∈ nondegeneratePieces L, P.Nondeg :=
  fun _ h ↦ (mem_nondegeneratePieces.mp h).2

theorem cover_nondegeneratePieces_subset (L : List Piece) :
    cover (nondegeneratePieces L) ⊆ cover L := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx
  exact mem_cover (mem_nondegeneratePieces.mp hP).1 hxP

theorem sum_nondegeneratePieces (L : List Piece) (F : Piece → ZMod 2)
    (hF : ∀ P, ¬ P.Nondeg → F P = 0) :
    ((nondegeneratePieces L).map F).sum = (L.map F).sum := by
  classical
  induction L with
  | nil => rfl
  | cons P L ih =>
    by_cases hP : P.Nondeg
    · simpa [nondegeneratePieces, hP] using congrArg (F P + ·) ih
    · simpa [nondegeneratePieces, hP, hF P hP] using ih

theorem isClosedChain_nondegeneratePieces {L : List Piece} (hL : IsClosedChain L) :
    IsClosedChain (nondegeneratePieces L) := by
  intro f
  rw [sum_nondegeneratePieces]
  · exact hL f
  · intro P hP
    have he : P.1 = P.2 := Classical.not_not.mp hP
    rw [he]
    exact add_self_zmod_two _

theorem parity_nondegeneratePieces (L : List Piece) (u x : Plane) :
    parity u (nondegeneratePieces L) x = parity u L x := by
  apply sum_nondegeneratePieces
  intro P hP
  have he : P.1 = P.2 := Classical.not_not.mp hP
  exact if_neg (not_crosses_of_level (congrArg (hgt u) he) x)

theorem exists_direction_nondegenerate (L : List Piece) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ P ∈ L, P.Nondeg → hgt u P.1 ≠ hgt u P.2 := by
  obtain ⟨u, hu, hL⟩ := exists_direction_hgt_ne _ (nondegeneratePieces_nondeg L)
  exact ⟨u, hu, fun P hP hnd ↦ hL P (mem_nondegeneratePieces.mpr ⟨hP, hnd⟩)⟩

theorem parity_eq_on_preconnected_complement {L : List Piece} (hclosed : IsClosedChain L)
    {u : Plane} (hu : Plane.IsDirection u)
    (hdir : ∀ P ∈ L, P.Nondeg → hgt u P.1 ≠ hgt u P.2)
    {S : Set Plane} (hS : IsPreconnected S) (havoid : Disjoint S (cover L))
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) : parity u L x = parity u L y := by
  rw [← parity_nondegeneratePieces L u x, ← parity_nondegeneratePieces L u y]
  exact parity_eq_of_isPreconnected hu
    (fun P hP ↦ hdir P (mem_nondegeneratePieces.mp hP).1 (mem_nondegeneratePieces.mp hP).2)
    (isClosedChain_nondegeneratePieces hclosed) hS
    (fun _ hz hzL ↦ Set.disjoint_left.mp havoid hz (cover_nondegeneratePieces_subset L hzL)) hx hy

end Reeken.Geometry
