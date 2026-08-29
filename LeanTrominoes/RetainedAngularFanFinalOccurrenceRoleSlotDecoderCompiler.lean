/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderCompiler
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotDecoderData

/-! # Compiler for aligned final occurrence-role and slot codes -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotDecoder

open Computability Turing

/-- Every unary code field decodes to its finite occurrence-role/slot pair in
linear time; oversized malformed fields saturate to the last finite code. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id pairs :=
  FiniteRoleSlotUnaryDecoder.computableInPolyTime

end LeanTrominoes.FinalOccurrenceRoleSlotDecoder

end
