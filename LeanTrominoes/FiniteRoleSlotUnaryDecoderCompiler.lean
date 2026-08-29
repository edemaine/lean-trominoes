/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time generic unary role/slot decoder -/

noncomputable section

namespace LeanTrominoes.FiniteRoleSlotUnaryDecoder

open Computability Turing

/-- Every unary code field decodes to its finite role/slot pair in linear
time; oversized malformed fields saturate to the last finite code. -/
noncomputable def computableInPolyTime
    {Role : Type} [Fintype Role] [Nonempty Role] [Inhabited Role] :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (pairs (Role := Role)) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      (zero (Role := Role)) transition finish)
    (fun _ => rfl) output_unaryFields

end LeanTrominoes.FiniteRoleSlotUnaryDecoder

end
