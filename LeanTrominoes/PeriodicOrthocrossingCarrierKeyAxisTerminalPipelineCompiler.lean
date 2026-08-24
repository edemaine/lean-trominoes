/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalTagCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Complete terminal carrier-key axis pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisTerminalPipeline

open Computability Turing

def fields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  TerminalCarrierKeyAxisStream.emittedFields
    (CarrierKeyAxisTerminalTags.tags input)

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      fields := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalCarrierKeyAxisStream.emittedFields
      (CarrierKeyAxisTerminalTags.tags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyAxisTerminalTags.tagsComputableInPolyTime
    TerminalCarrierKeyAxisStream.emittedFieldsComputableInPolyTime

end CarrierKeyAxisTerminalPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
