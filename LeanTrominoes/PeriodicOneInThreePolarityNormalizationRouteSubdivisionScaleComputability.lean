/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.Computability

/-! # Routed-polarity polyline scaling computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Uniform scaling of a finite polyline is primitive recursive. -/
theorem scalePolyline_primrec : Primrec₂ scalePolyline := by
  change Primrec fun input : Int × List Cell =>
    scalePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_scale_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
