/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverRouteTailRecordSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverSlotInputSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Phase.PeriodicCNFStripDirectSourceFinalPhaseRouteTailRecordData

/-! # Semantics of the direct-source crossover route-tail phase -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCrossoverPhaseRouteTailVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The filtered crossover token stream is exactly the semantic record word
for the globally indexed crossover prefix. -/
theorem directSourceFinalCrossoverRouteTailRecordTokens_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalCrossoverRouteTailRecordTokens decider symbols =
      retainedDirectClauseRouteTailRecordStream
        (((directSourceFinalCrossoverClauses decider symbols).zipIdx 0).map
          fun taggedClause =>
            retainedFinalDirectClauseRouteTailRecordQuery
              (directSourceFormula decider symbols)
              taggedClause.2 ⟨(0, 0), taggedClause.1⟩) := by
  unfold directSourceFinalCrossoverRouteTailRecordTokens
    directSourceFinalCrossoverRouteTailRecordSlotInputs
  rw [retainedDirectCrossoverRouteTailRecordSlotInputs_directSource_eq,
    directSourceFinalCrossoverRouteTailRecordQueries_eq_semantic]

end LeanTrominoes.PeriodicCNFStripReduction

end
