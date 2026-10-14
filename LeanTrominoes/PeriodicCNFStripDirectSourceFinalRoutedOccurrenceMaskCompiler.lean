/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryCompiler
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the routed-family occurrence-mask suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directSourceFinalRoutedOccurrenceMaskSuffixComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool
      id id (directSourceFinalRoutedOccurrenceMaskSuffix decider) :=
  TM2ListAppend.nativeComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime
        (directRetainedFinalRoutedClauseQueriesComputableInPolyTime decider)
        retainedFinalCopiedClauseDescriptorsComputableInPolyTime)
      (descriptorOccurrenceMaskComputableInPolyTime false))
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime
        (directRetainedFinalRoutedVariableClauseQueriesComputableInPolyTime
          decider)
        retainedFinalCopiedClauseDescriptorsComputableInPolyTime)
      (descriptorOccurrenceMaskComputableInPolyTime false))

end LeanTrominoes.PeriodicCNFStripReduction

end
