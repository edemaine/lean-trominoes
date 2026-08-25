/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineData
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Compiler for the physical carrier boundary-presence pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

noncomputable def terminalFieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalFields := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => GuardedPresenceFieldProjector.output false
      (CarrierActiveKeyRecipeStream.terminalTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierActiveKeyRecipeStream.terminalTokensComputableInPolyTime
    (GuardedPresenceFieldProjector.computableInPolyTime false)

noncomputable def crossingFieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingFields := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => GuardedPresenceFieldProjector.output true
      (CarrierActiveKeyRecipeStream.crossingTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierActiveKeyRecipeStream.crossingTokensComputableInPolyTime
    (GuardedPresenceFieldProjector.computableInPolyTime true)

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      fields := by
  let joined := TM2ListAppend.computableInPolyTime
    terminalFieldsComputableInPolyTime crossingFieldsComputableInPolyTime
  let appended := TM2CompositionMachine.computableInPolyTime joined
    (TM2ListAppend.appendFixedComputableInPolyTime
      [UnaryFieldEncoderMachine.Symbol.delimiter])
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2ListAppend.appendFixedWords
      [UnaryFieldEncoderMachine.Symbol.delimiter]
      (terminalFields input ++ crossingFields input))
  exact appended

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing

end
