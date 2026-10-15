/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Routed.PeriodicCNFStripDirectSourceFinalRoutedClauseQuerySemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Copied.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices

/-! # Successful final route choices of direct-source routed clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
