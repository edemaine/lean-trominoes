/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordCompiler

/-! # Compiling direct retained carrier descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCarrierCompiledStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedCarrierCompiledVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Reinterpret the exact direct binary-word output as its semantic numeric
route-descriptor list under the carrier compiler's canonical encoding. -/
private noncomputable def directSourceNumericRouteDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RouteDescriptor)
      encoding.Γ DelimitedBinaryWords.Token id
      CarrierRankOrderedPairs.InputEncoding
      (fun symbols =>
        numericRouteDescriptors (directSourceFormula decider symbols)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceRouteDescriptorBinaryWordsComputableInPolyTime decider)
    (directSourceRouteDescriptorBinaryWords_encode_eq_carrierInput decider)

/-- Compile exact direct-source routes, then execute the complete
rank-ordered retained carrier descriptor scan. -/
noncomputable def
    directRetainedPlanarMetadataCompiledCarrierClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledCarrierClauseDescriptorCompiler
      decider := by
  let routes := directSourceNumericRouteDescriptorsComputableInPolyTime decider
  let carriers :=
    FormulaShapeRetainedPlanarMetadataDirection.rankOrderedCarrierLinkDescriptorScanComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime routes carriers
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
