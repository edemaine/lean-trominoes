/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendOccurrenceMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the carrier/bend/routed occurrence-mask suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directSourceFinalCarrierOccurrenceMaskSuffixComputableInPolyTime
    (carrierActive bendActive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool
      id id
      (directSourceFinalCarrierOccurrenceMaskSuffix
        decider carrierActive bendActive) :=
  TM2ListAppend.nativeComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directRetainedPlanarMetadataCarrierClauseDescriptorsComputableInPolyTime
        decider)
      (descriptorOccurrenceMaskComputableInPolyTime carrierActive))
    (directSourceFinalBendOccurrenceMaskSuffixComputableInPolyTime
      decider bendActive)

end LeanTrominoes.PeriodicCNFStripReduction

end
