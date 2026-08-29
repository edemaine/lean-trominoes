/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedOccurrenceMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the bend-and-routed occurrence-mask suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendOccurrenceMaskStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalBendOccurrenceMaskSuffixComputableInPolyTime
    (bendActive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool
      id id
      (directSourceFinalBendOccurrenceMaskSuffix decider bendActive) :=
  TM2ListAppend.nativeComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directRetainedPlanarMetadataBaseBendClauseDescriptorsComputableInPolyTime
        decider)
      (descriptorOccurrenceMaskComputableInPolyTime bendActive))
    (directSourceFinalRoutedOccurrenceMaskSuffixComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
