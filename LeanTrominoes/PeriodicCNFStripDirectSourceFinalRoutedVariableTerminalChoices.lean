/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices

/-! # Successful final route choices of direct-source routed variables -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableChoicesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableChoicesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every incidence in the final routed-variable suffix selects a direct
atlas route. -/
theorem directSourceFinalRoutedVariableRouteChoices
    (symbols : List encoding.Γ) :
    FinalIndexedClauseRouteChoices
      (directSourceFinalNormalizedFormula decider symbols)
      (directSourceFinalRoutedVariableStart decider symbols)
      (directSourceFinalRoutedVariableClauses decider symbols) :=
  finalIndexedClauseRouteChoices_of_allDirect
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalRoutedVariableStart decider symbols)
    (directSourceFinalRoutedVariableClauses decider symbols)
    (directSourceFinalRoutedVariableClauses_nonempty decider symbols)
    (directSourceFinalRoutedVariableClauses_widthAtMostThree decider symbols)
    (directSourceFinalIndexedRoutedVariableQueriesAllDirect
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
