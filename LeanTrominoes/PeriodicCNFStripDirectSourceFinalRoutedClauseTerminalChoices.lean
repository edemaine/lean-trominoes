/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices

/-! # Successful final route choices of direct-source routed clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseChoicesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseChoicesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every incidence in the final routed-clause family selects a direct atlas
route. -/
theorem directSourceFinalRoutedClauseRouteChoices
    (symbols : List encoding.Γ) :
    FinalIndexedClauseRouteChoices
      (directSourceFinalNormalizedFormula decider symbols)
      (directSourceFinalRoutedClauseStart decider symbols)
      (directSourceFinalRoutedClauseClauses decider symbols) :=
  finalIndexedClauseRouteChoices_of_allDirect
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalRoutedClauseStart decider symbols)
    (directSourceFinalRoutedClauseClauses decider symbols)
    (directSourceFinalRoutedClauseClauses_nonempty decider symbols)
    (directSourceFinalRoutedClauseClauses_widthAtMostThree decider symbols)
    (directSourceFinalIndexedRoutedClauseQueriesAllDirect
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
