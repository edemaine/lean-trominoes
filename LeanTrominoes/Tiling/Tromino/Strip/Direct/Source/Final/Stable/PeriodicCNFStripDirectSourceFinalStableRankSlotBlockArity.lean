/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyArity
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Stable.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockLength

/-! # Query arities of direct-source stable-rank slot blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalSlotBlockArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalQueryArity_eq_stableRankSlotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedFinalClauseQueryAssembly decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity =
      (directSourceFinalStableRankSlotBlocks decider symbols).map
        List.length := by
  exact
    (directRetainedFinalClauseQueryAssembly_arities_eq_clauseLengths
      decider symbols).trans
    (directSourceFinalStableRankSlotBlocks_lengths decider symbols).symm

theorem directSourceFinalQuery_length_eq_stableRankSlotBlocks
    (symbols : List encoding.Γ) :
    (directRetainedFinalClauseQueryAssembly decider symbols).length =
      (directSourceFinalStableRankSlotBlocks decider symbols).length := by
  simpa only [List.length_map] using congrArg List.length
    (directSourceFinalQueryArity_eq_stableRankSlotBlockLengths
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
