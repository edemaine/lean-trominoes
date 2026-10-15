/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryCompiler
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Compiling the five-family final clause-query assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile the two direct routed families and append their outputs. -/
noncomputable def
    directRetainedFinalRoutedClauseQuerySuffixComputableInPolyTime :
    DirectRetainedFinalRoutedClauseQuerySuffixCompiler decider :=
  TM2ListAppend.nativeComputableInPolyTime
    (directRetainedFinalRoutedClauseQueriesComputableInPolyTime decider)
    (directRetainedFinalRoutedVariableClauseQueriesComputableInPolyTime
      decider)

/-- Prepend the fallback bend family. -/
noncomputable def
    directRetainedFinalBendClauseQuerySuffixComputableInPolyTime :
    DirectRetainedFinalBendClauseQuerySuffixCompiler decider :=
  TM2ListAppend.nativeComputableInPolyTime
    (directRetainedFinalBendClauseQueriesComputableInPolyTime decider)
    (directRetainedFinalRoutedClauseQuerySuffixComputableInPolyTime decider)

/-- Prepend the fallback carrier family. -/
noncomputable def
    directRetainedFinalCarrierClauseQuerySuffixComputableInPolyTime :
    DirectRetainedFinalCarrierClauseQuerySuffixCompiler decider :=
  TM2ListAppend.nativeComputableInPolyTime
    (directRetainedFinalCarrierClauseQueriesComputableInPolyTime decider)
    (directRetainedFinalBendClauseQuerySuffixComputableInPolyTime decider)

/-- Prepend the fixed direct crossover family to obtain the complete
five-family query assembly. -/
noncomputable def
    directRetainedFinalClauseQueryAssemblyComputableInPolyTime :
    DirectRetainedFinalClauseQueryAssemblyCompiler decider :=
  TM2ListAppend.nativeComputableInPolyTime
    (directRetainedFinalCrossoverClauseQueriesComputableInPolyTime decider)
    (directRetainedFinalCarrierClauseQuerySuffixComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
