/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueData

/-! # Physical compiler for padded crossing carrier-key axis fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing

def crossingCarrierKeyAxisCompiledFields
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FixedAxisUnaryFields.compiledFields crossingCarrierKeyRecipeAxes
    (crossingCarrierKeyExpandedActives tokens)

noncomputable def crossingCarrierKeyAxisCompiledFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      crossingCarrierKeyAxisCompiledFields := by
  change TM2ComputableInPolyTime id id
    (fun tokens =>
      FixedAxisUnaryFields.compiledFields crossingCarrierKeyRecipeAxes
        (crossingCarrierKeyExpandedActives tokens))
  exact FixedAxisUnaryFields.afterComputableInPolyTime id
    crossingCarrierKeyRecipeAxes crossingCarrierKeyExpandedActives
    crossingCarrierKeyExpandedActivesComputableInPolyTime

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
