/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSelectedOccurrenceInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Computability of one variable-fan polarity -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonPolarityComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonPolarityComputed := by
  exact occurrencePolarity_primrec.comp
    horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
