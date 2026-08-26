/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordCompiler

/-! # Direct numeric incidence-route descriptor compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceNumericRouteDescriptorCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceNumericRouteDescriptorCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Reinterpret the exact direct binary-word output as its semantic numeric
incidence-route descriptor list under the canonical carrier encoding. -/
noncomputable def directSourceNumericRouteDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RouteDescriptor)
      encoding.Γ DelimitedBinaryWords.Token id
      CarrierRankOrderedPairs.InputEncoding
      (fun symbols =>
        numericRouteDescriptors (directSourceFormula decider symbols)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceRouteDescriptorBinaryWordsComputableInPolyTime decider)
    (directSourceRouteDescriptorBinaryWords_encode_eq_carrierInput decider)

end PeriodicCNFStripReduction
end LeanTrominoes
