import Reeken.Nonstandard.LoopContraction
import Reeken.Geometry.PolygonEars

/-! # Simple connectivity of the standard inside

The inner-polygon construction contains every compact loop in a finite polygon
whose closed inside stays in the standard inside. The finite ear theorem and
contraction induction now discharge the polygonal hypothesis of that NSA step.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

theorem isSimplyConnected_standardInside {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
    (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
    (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple) : IsSimplyConnected (standardInside p) :=
  isSimplyConnected_standardInside_of_closed_polygon p hmax hs contractibleSpace_closed_inside

end Reeken.NSA
