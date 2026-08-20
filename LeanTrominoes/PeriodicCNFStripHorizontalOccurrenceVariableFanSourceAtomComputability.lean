/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSourceComputability

/-! # Computability of the variable-fan source atom -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonSourceAtom_primrec :
    Primrec fun input : HorizontalVariableRibbonFanInput =>
      (horizontalOccurrenceVariableSourceComputed input, input.2) :=
  Primrec.pair horizontalOccurrenceVariableSourceComputed_primrec Primrec.snd

end PeriodicCNFStripReduction
end LeanTrominoes
