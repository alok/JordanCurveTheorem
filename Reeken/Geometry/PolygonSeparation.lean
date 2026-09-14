import Reeken.Geometry.SimplePolygon
import Schoenflies.PrePolygonSep

/-! # The finite polygonal Jordan theorem for Reeken's polygons

The finite theorem is supplied by the vendored collar/parity proof. This adapter
uses only the polygon's actual vertex and edge simplicity properties.
-/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Schoenflies.Plane}

def cyclicIndex (p : InscribedPolygon f) (hn : 2 ≤ p.n)
    (i : ZMod (p.n - 2 + 3)) : Fin (p.n + 1) :=
  Fin.cast (by omega) i

theorem cyclicIndex_injective (p : InscribedPolygon f) (hn : 2 ≤ p.n) :
    Function.Injective (p.cyclicIndex hn) := Fin.cast_injective (by omega)

theorem cyclicIndex_add_one (p : InscribedPolygon f) (hn : 2 ≤ p.n)
    (i : ZMod (p.n - 2 + 3)) :
    p.cyclicIndex hn (i + 1) = nextIndex p.n (p.cyclicIndex hn i) := by
  apply Fin.ext
  have hsize : p.n - 2 + 3 = p.n + 1 := by omega
  have hi := ZMod.val_lt i
  have hval : ∀ j : ZMod (p.n - 2 + 3), (p.cyclicIndex hn j).val = j.val := fun _ ↦ rfl
  rw [hval, nextIndex_val, hval, ZMod.val_add, ZMod.val_one_eq_one_mod]
  rw [Nat.mod_eq_of_lt (by omega : 1 < p.n - 2 + 3)]
  split_ifs with hlast
  · rw [hlast, ← hsize, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

noncomputable def toPrePolygon (p : InscribedPolygon f) (hn : 2 ≤ p.n) (hp : p.Simple) :
    Schoenflies.PrePolygon (p.n - 2) where
  vertex i := p.vertex (p.cyclicIndex hn i)
  vertex_inj := p.vertex_injective.comp (p.cyclicIndex_injective hn)
  edges_meet i j hij := by
    intro x hx
    rw [p.cyclicIndex_add_one hn i, p.cyclicIndex_add_one hn j] at hx
    have hij' : p.cyclicIndex hn i ≠ p.cyclicIndex hn j :=
      fun he ↦ hij (p.cyclicIndex_injective hn he)
    rcases hp.2 _ _ hij' x hx with ⟨hi, hxi⟩ | ⟨_, hxj⟩
    · right
      rwa [mem_singleton_iff, p.cyclicIndex_add_one hn i, hi]
    · exact Or.inl hxj

theorem toPrePolygon_carrier (p : InscribedPolygon f) (hn : 2 ≤ p.n) (hp : p.Simple) :
    (p.toPrePolygon hn hp).carrier = p.trace := by
  have hsurj : Function.Surjective (p.cyclicIndex hn) := by
    intro i
    exact ⟨Fin.cast (by omega) i, Fin.ext rfl⟩
  ext x
  simp only [Schoenflies.PrePolygon.carrier, Schoenflies.PrePolygon.edge, toPrePolygon,
    trace, mem_iUnion, cyclicIndex_add_one]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨p.cyclicIndex hn i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := hsurj i
    exact ⟨j, hi⟩

theorem Simple.isSeparating {p : InscribedPolygon f} (hp : p.Simple) (hn : 2 ≤ p.n) :
    Schoenflies.IsSeparating p.trace := by
  rw [← p.toPrePolygon_carrier hn hp]
  exact (p.toPrePolygon hn hp).isSeparating_carrier

end Reeken.Geometry.InscribedPolygon
