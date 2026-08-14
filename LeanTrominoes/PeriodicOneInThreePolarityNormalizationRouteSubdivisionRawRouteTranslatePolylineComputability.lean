/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionBasicComputability

/-! # Raw-route polyline translation computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

theorem translatePolyline_primrec :
    Primrec₂ PeriodicOrthocrossing.translatePolyline := by
  change Primrec fun input : Cell × List Cell =>
    PeriodicOrthocrossing.translatePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
