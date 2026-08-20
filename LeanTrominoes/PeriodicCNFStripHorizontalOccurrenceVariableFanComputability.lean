/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCodeComputability

/-! # Computability of horizontal variable-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : DecidableEq VariableRibbonFanCode := Classical.decEq _
local instance : Inhabited VariableRibbonFanData :=
  ⟨variableRibbonFanDataOfCode default⟩

theorem horizontalOccurrenceVariableRibbonFanDataComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonFanDataComputed := by
  have decode : Primrec variableRibbonFanDataOfCode :=
    Computability.finiteDomain_primrec _
  exact decode.comp
    horizontalOccurrenceVariableRibbonFanCodeComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
