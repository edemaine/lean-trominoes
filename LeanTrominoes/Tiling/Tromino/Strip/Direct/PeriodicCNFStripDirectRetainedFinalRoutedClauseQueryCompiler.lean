/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryData
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling direct final routed-clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Exact source clause profiles compose with the fixed stable direct-query
block map. -/
noncomputable def
    directRetainedFinalRoutedClauseQueriesComputableInPolyTime :
    DirectRetainedFinalRoutedClauseQueryCompiler decider := by
  let profiles := directSourceFormulaClauseProfilesComputableInPolyTime
    decider
  let queries := FiniteBlockTransducer.computableInPolyTime
    directRetainedFinalRoutedClauseQueryBlock
  let complete :=
    TM2CompositionMachine.computableInPolyTime profiles queries
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicEightOccurrenceSplit.RetainedFinalCopiedClauseQuery)
    encoding.Γ
    PeriodicEightOccurrenceSplit.RetainedFinalCopiedClauseQuery id id
    (fun symbols =>
      (directSourceFormulaClauseProfiles decider symbols).flatMap
        directRetainedFinalRoutedClauseQueryBlock)
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
