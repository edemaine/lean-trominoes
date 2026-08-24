/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingPipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalPipelineCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Complete padded carrier-key axis pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisPipeline

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def fields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyAxisTerminalPipeline.fields input ++
    CarrierKeyAxisCrossingPipeline.fields input

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      fields := by
  exact TM2ListAppend.computableInPolyTime
    CarrierKeyAxisTerminalPipeline.fieldsComputableInPolyTime
    CarrierKeyAxisCrossingPipeline.fieldsComputableInPolyTime

end CarrierKeyAxisPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
