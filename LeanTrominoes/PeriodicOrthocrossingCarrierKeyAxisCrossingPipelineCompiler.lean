/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingTagCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Complete crossing carrier-key axis pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisCrossingPipeline

open Computability Turing

def fields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CrossingCarrierKeyAxisStream.emittedFields
    (CarrierKeyAxisCrossingTags.tags input)

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      fields := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingCarrierKeyAxisStream.emittedFields
      (CarrierKeyAxisCrossingTags.tags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyAxisCrossingTags.tagsComputableInPolyTime
    CrossingCarrierKeyAxisStream.emittedFieldsComputableInPolyTime

end CarrierKeyAxisCrossingPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
