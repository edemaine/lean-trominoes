/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionCompiler
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyAllFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupInput
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for representative carrier source-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeFieldLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  fun descriptors =>
    DelimitedBinaryWords.encode
      (RouteDescriptorBinaryWords.words descriptors)

noncomputable def expandedRowsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      DelimitedBinaryWords.finEncoding.encode expandedRows := by
  let expander := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.encode
    (DelimitedBinaryWordFixedFieldRowExpansion.tokensComputableInPolyTime
      fieldCount)
    (fun _ => rfl) (fun _ => rfl)
  let compiled := TM2CompositionMachine.computableInPolyTime
    paddedCarrierSourceKeyRepresentativeRowsComputableInPolyTime
    expander
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun descriptors =>
      DelimitedBinaryWordFixedFieldRowExpansion.tokens_encode fieldCount
        (paddedCarrierSourceKeyRepresentativeRows descriptors))

noncomputable def alignedFieldValuesComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields alignedFieldValues :=
  TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    CarrierSourceKeyAllFieldStream.emittedFieldsComputableInPolyTime
    CarrierSourceKeyAllFieldStream.emittedFields_eq

noncomputable def inputComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      LastTrueUnaryValueLookupMachine.encode input := by
  let paired := TM2ForkMachine.computableInPolyTime
    expandedRowsComputableInPolyTime
    alignedFieldValuesComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

/-- All twelve fields of every stable carrier source-key representative are
polynomial-time computable. -/
noncomputable def selectedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields selectedFields :=
  LastTrueUnaryValueLookupMachine.afterComputableInPolyTime
    descriptorInputEncoding input inputComputableInPolyTime

end CarrierSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing

end
