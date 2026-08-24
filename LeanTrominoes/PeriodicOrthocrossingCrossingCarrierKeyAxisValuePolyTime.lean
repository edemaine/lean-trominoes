/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsExactCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueLength

/-! # Polynomial-time padded crossing carrier-key axis fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing

/-- The per-slot-pair compiler emits the canonical unary encoding of every
padded crossing candidate's zero-or-one axis value. -/
noncomputable def crossingCarrierKeyAxisValuesComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields
      crossingCarrierKeyAxisValues := by
  unfold crossingCarrierKeyAxisValues
  exact FixedAxisUnaryFields.afterExactComputableInPolyTime id
    crossingCarrierKeyRecipeAxes crossingCarrierKeyExpandedActives
    crossingCarrierKeyExpandedActivesComputableInPolyTime
    crossingCarrierKeyExpandedActives_axis_length

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
