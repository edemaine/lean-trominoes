/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsExactCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueLength

/-! # Polynomial-time padded terminal carrier-key axis fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- The per-pair compiler emits the canonical unary encoding of every padded
terminal candidate's zero-or-one axis value. -/
noncomputable def terminalCarrierKeyAxisValuesComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields
  terminalCarrierKeyAxisValues := by
  unfold terminalCarrierKeyAxisValues
  exact FixedAxisUnaryFields.afterExactComputableInPolyTime id
    terminalCarrierKeyRecipeAxes terminalCarrierKeyExpandedActives
    terminalCarrierKeyExpandedActivesComputableInPolyTime
    terminalCarrierKeyExpandedActives_axis_length

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
