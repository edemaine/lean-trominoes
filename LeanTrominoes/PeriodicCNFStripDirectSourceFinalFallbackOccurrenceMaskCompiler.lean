/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryCompiler
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling fallback-family occurrence-slot masks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFallbackOccurrenceMaskCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compile the complete five-family occurrence mask with independently
chosen carrier and bend values. -/
noncomputable def
    directSourceFinalFallbackOccurrenceMaskComputableInPolyTime
    (carrierActive bendActive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool
      id id
      (directSourceFinalFallbackOccurrenceMask
        decider carrierActive bendActive) := by
  unfold directSourceFinalFallbackOccurrenceMask
  exact TM2ListAppend.nativeComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime
        (directRetainedFinalCrossoverClauseQueriesComputableInPolyTime decider)
        retainedFinalCopiedClauseDescriptorsComputableInPolyTime)
      (descriptorOccurrenceMaskComputableInPolyTime false))
    (directSourceFinalCarrierOccurrenceMaskSuffixComputableInPolyTime
      decider carrierActive bendActive)

end LeanTrominoes.PeriodicCNFStripReduction

end
