/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendFallbackRecordProfileSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRecordRouteSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteTailRecordCompiler

/-! # Semantics of compiled normalized bend fallback records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The normalized bend compiler reconstructs the exact declarative
batch-formatter input for the normalized bend blocks. -/
theorem directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
        decider symbols =
      directSourceFinalBendNormalizedFallbackRecordInputTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
    directSourceFinalBendNormalizedFallbackRecordInputTokens
  rw [directSourceFinalBendFallbackCompiledRecordProfiles_eq,
    directSourceFinalBendNormalizedFallbackRouteDirections_eq_blockRoutes,
    ← directSourceFinalBendNormalizedFallbackRecordBlockProfiles_eq]
  exact BinaryRouteTailRecordProfileFraming.framed_blockProfiles_blockRoutes _

/-- Consequently the polynomial-time bend compiler emits the exact normalized
declarative fallback record stream. -/
theorem directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
        decider symbols =
      directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
  rw [directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens_eq,
    directSourceFinalBendNormalizedFallbackRecordFormatter_output]

end LeanTrominoes.PeriodicCNFStripReduction

end
