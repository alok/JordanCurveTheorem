import Reeken.Geometry.ChosenArcs
import Reeken.Nonstandard.PolygonArcs

/-! # Uniform infinitesimal control of the chosen boundary arcs

The arc choice is fixed at each finite index. Lemma 1(iii) makes that chosen arc
infinitesimal for every near pair. Universal transfer upgrades this to a bound
uniform over all edges of an internal finite chain.
-/

open Filter Set Metric Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem ordered_chosenArc_inMonad
    (a b : (i : ℕ) → Fin ((p i).n + 1)) (hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i)
    (hne : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i)))
      (ofSeq (fun i ↦ (p i).vertex (b i)))) :
    InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ cover ((p i).chosenArcPieces (a i) (b i))))
      (ofSeq (fun i ↦ (p i).vertex (a i))) := by
  rw [inMonad_internalSet_iff]
  intro ε hε
  rcases (exactly_one_vertex_arc_small p a b hmax hab hne).1 with hF | hB
  · have hb := (inMonad_internalSet_iff _ _).mp hF ε hε
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hab, hb] with i hsi hni habi hbi
    have hn : 2 ≤ (p i).n := by omega
    rw [InscribedPolygon.chosenArcPieces, dif_pos ⟨hn, hsi⟩, if_pos habi]
    exact fun _ hx ↦ (p i).orderedSmallArcPieces_subset_ball hn hsi habi (Or.inl hbi) hx
  · have hb := (inMonad_internalSet_iff _ _).mp hB ε hε
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hab, hb] with i hsi hni habi hbi
    have hn : 2 ≤ (p i).n := by omega
    rw [InscribedPolygon.chosenArcPieces, dif_pos ⟨hn, hsi⟩, if_pos habi]
    exact fun _ hx ↦ (p i).orderedSmallArcPieces_subset_ball hn hsi habi (Or.inr hbi) hx

theorem chosenArc_inMonad
    (a b : (i : ℕ) → Fin ((p i).n + 1))
    (hne : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i)))
      (ofSeq (fun i ↦ (p i).vertex (b i)))) :
    InMonad (internalSet (U := hyperfilter ℕ) (fun i ↦ cover ((p i).chosenArcPieces (a i) (b i))))
      (ofSeq (fun i ↦ (p i).vertex (a i))) := by
  by_cases hab : ∀ᶠ i in hyperfilter ℕ, a i ≤ b i
  · exact ordered_chosenArc_inMonad p hmax hs a b hab hne
  · have hba : ∀ᶠ i in hyperfilter ℕ, b i ≤ a i :=
      (Ultrafilter.eventually_not.mpr hab).mono fun _ hi ↦ le_of_not_ge hi
    have h := (ordered_chosenArc_inMonad p hmax hs b a hba hne.symm).change_center hne.symm
    apply h.mono
    apply (internalSet_subset _ _).mpr
    exact Eventually.of_forall fun i ↦ (congrArg cover ((p i).chosenArcPieces_symm (a i) (b i))).subset

theorem chosenArcs_uniformly_small (L : ℕ → List Piece)
    (a b : (i : ℕ) → Piece → Fin ((p i).n + 1))
    (hne : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i,
      dist ((p i).vertex (a i P)) ((p i).vertex (b i P)) < η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i,
      ∀ z ∈ cover ((p i).chosenArcPieces (a i P) (b i P)),
        dist z ((p i).vertex (a i P)) < η := by
  intro η hη
  by_contra h
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ d : Piece × Plane,
      d.1 ∈ L i ∧ d.2 ∈ cover ((p i).chosenArcPieces (a i d.1) (b i d.1)) ∧
        η ≤ dist d.2 ((p i).vertex (a i d.1)) := by
    filter_upwards [Ultrafilter.eventually_not.mpr h] with i hi
    push Not at hi
    obtain ⟨P, hP, z, hz, hdist⟩ := hi
    exact ⟨(P, z), hP, hz, hdist⟩
  obtain ⟨d, hd⟩ := (exists_holds (U := hyperfilter ℕ) (fun i (d : Piece × Plane) ↦
    d.1 ∈ L i ∧ d.2 ∈ cover ((p i).chosenArcPieces (a i d.1) (b i d.1)) ∧
      η ≤ dist d.2 ((p i).vertex (a i d.1)))).mpr hex
  star_cases d
  have hn : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i (d i).1)))
      (ofSeq (fun i ↦ (p i).vertex (b i (d i).1))) := by
    intro ε hε
    exact ((hne ε hε).and hd).mono fun i hi ↦ hi.1 _ hi.2.1
  have hsmall := chosenArc_inMonad p hmax hs (fun i ↦ a i (d i).1) (fun i ↦ b i (d i).1) hn
  have hz := hsmall (ofSeq (fun i ↦ (d i).2)) (hd.mono fun _ hi ↦ hi.2.1)
  obtain ⟨i, hlt, hge⟩ := ((hz η hη).and (hd.mono fun _ hi ↦ hi.2.2)).exists
  exact hlt.not_ge hge

end Reeken.NSA
