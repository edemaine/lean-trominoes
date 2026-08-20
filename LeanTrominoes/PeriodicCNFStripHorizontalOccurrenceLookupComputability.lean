/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceLookupInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of normalized occurrence lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceLookupComputed_primrec :
    Primrec horizontalOccurrenceLookupComputed := by
  exact occurrenceAt_primrec.comp horizontalOccurrenceLookupInput_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
