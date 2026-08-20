/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanCodeComputability

/-! # Computability of horizontal clause-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : DecidableEq HorizontalClauseRibbonFanCode := Classical.decEq _
local instance : Inhabited ClauseRibbonFanData :=
  ⟨horizontalOccurrenceClauseRibbonFanDataOfCode default⟩

theorem horizontalOccurrenceClauseRibbonFanDataComputed_primrec :
    Primrec horizontalOccurrenceClauseRibbonFanDataComputed := by
  have decode : Primrec horizontalOccurrenceClauseRibbonFanDataOfCode :=
    Computability.finiteDomain_primrec _
  exact decode.comp horizontalOccurrenceClauseRibbonFanCodeComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
