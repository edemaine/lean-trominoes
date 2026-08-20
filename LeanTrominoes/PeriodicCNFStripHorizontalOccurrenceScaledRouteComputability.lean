/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceStoredRouteComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionScaleComputability

/-! # Computability of doubled horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalOccurrenceScaledRouteComputed_primrec :
    Primrec horizontalOccurrenceScaledRouteComputed := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.scalePolyline_primrec.comp
      (Primrec.const (2 : Int))
      horizontalOccurrenceStoredRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
