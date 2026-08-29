/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices

/-! # Successful final route choices of direct-source crossovers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverChoicesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverChoicesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every indexed incidence in the final crossover prefix selects a direct
atlas route. -/
theorem directSourceFinalCrossoverRouteChoices
    (symbols : List encoding.Γ) :
    FinalIndexedClauseRouteChoices
      (directSourceFormula decider symbols) 0
      (directSourceFinalCrossoverClauses decider symbols) :=
  finalIndexedClauseRouteChoices_of_allDirect
    (directSourceFormula decider symbols) 0
    (directSourceFinalCrossoverClauses decider symbols)
    (directSourceFinalCrossoverClauses_nonempty decider symbols)
    (directSourceFinalCrossoverClauses_widthAtMostThree decider symbols)
    (directSourceFinalIndexedCrossoverClauseQueriesAllDirect
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
