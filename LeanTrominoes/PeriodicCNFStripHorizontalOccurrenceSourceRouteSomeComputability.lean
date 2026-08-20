/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceTranslationComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceReversedRouteComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteTranslatePolylineComputability

/-! # Computability of found horizontal occurrence source routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalOccurrenceSourceRouteSomeComputed_primrec :
    Primrec horizontalOccurrenceSourceRouteSomeComputed := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.translatePolyline_primrec.comp
      horizontalOccurrenceTranslationComputed_primrec
      horizontalOccurrenceReversedRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
