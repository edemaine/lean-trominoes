/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Compiler for padded terminal carrier-key axis fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- Physical finite-control output before its exact-length semantics is used. -/
def terminalCarrierKeyAxisCompiledFields
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FixedAxisUnaryFields.compiledFields terminalCarrierKeyRecipeAxes
    (terminalCarrierKeyExpandedActives tokens)

/-- Runtime activations followed by the fixed axis adapter are polynomial
time on one tagged descriptor pair. -/
noncomputable def terminalCarrierKeyAxisCompiledFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      terminalCarrierKeyAxisCompiledFields := by
  change TM2ComputableInPolyTime id id
    (fun tokens =>
      FixedAxisUnaryFields.compiledFields terminalCarrierKeyRecipeAxes
        (terminalCarrierKeyExpandedActives tokens))
  exact FixedAxisUnaryFields.afterComputableInPolyTime id
    terminalCarrierKeyRecipeAxes terminalCarrierKeyExpandedActives
    terminalCarrierKeyExpandedActivesComputableInPolyTime

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
