/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldData
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Fixed-list composition for compiled carrier rank-datum fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  fun descriptors =>
    DelimitedBinaryWords.encode
      (RouteDescriptorBinaryWords.words descriptors)

/-- Reinterpret an existing unary field compiler as the encoded singleton
column selected by one member of the fixed field index. -/
noncomputable def singletonComputableInPolyTime
    (field : Field)
    (compiler :
      TM2ComputableInPolyTime descriptorInputEncoding
        UnaryFieldEncoderMachine.unaryFields field.values) :
    TM2ComputableInPolyTime descriptorInputEncoding id
      (encodedFields [field]) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun _ => by simp [encodedFields])

/-- Prepend one verified column compiler to a verified fixed field-list
compiler. -/
noncomputable def prependComputableInPolyTime
    (field : Field) {fields : List Field}
    (fieldCompiler :
      TM2ComputableInPolyTime descriptorInputEncoding
        UnaryFieldEncoderMachine.unaryFields field.values)
    (fieldsCompiler :
      TM2ComputableInPolyTime descriptorInputEncoding id
        (encodedFields fields)) :
    TM2ComputableInPolyTime descriptorInputEncoding id
      (encodedFields (field :: fields)) := by
  let fieldTokens :
      TM2ComputableInPolyTime descriptorInputEncoding id
        (fun descriptors => UnaryFieldEncoderMachine.unaryFields
          (field.values descriptors)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun descriptors => UnaryFieldEncoderMachine.unaryFields
        (field.values descriptors))
      fieldCompiler (fun _ => rfl)
  exact TM2ListAppend.computableInPolyTime fieldTokens fieldsCompiler

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
