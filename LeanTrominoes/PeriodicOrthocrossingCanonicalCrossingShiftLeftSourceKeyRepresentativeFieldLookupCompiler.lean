/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionCompiler
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyAllFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupInput
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for representative canonical crossing source-pair fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  CanonicalCrossingShiftLeftSourceKeyRepresentatives.descriptorInputEncoding

noncomputable def expandedRowsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      DelimitedBinaryWords.finEncoding.encode expandedRows := by
  let expander := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.encode
    (DelimitedBinaryWordFixedFieldRowExpansion.tokensComputableInPolyTime
      fieldCount)
    (fun _ => rfl) (fun _ => rfl)
  let compiled := TM2CompositionMachine.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyRepresentatives.representativeRowsComputableInPolyTime
    expander
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun descriptors => by
      exact
        DelimitedBinaryWordFixedFieldRowExpansion.tokens_encode fieldCount
          (CanonicalCrossingShiftLeftSourceKeyRepresentatives.representativeRows
            descriptors))

noncomputable def alignedFieldValuesComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields alignedFieldValues := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    CanonicalCrossingShiftLeftSourceKeyAllFieldStream.emittedFieldsComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (fun descriptors =>
      CanonicalCrossingShiftLeftSourceKeyAllFieldStream.emittedFields_descriptorWords
        descriptors)

noncomputable def inputComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      LastTrueUnaryValueLookupMachine.encode input := by
  let paired := TM2ForkMachine.computableInPolyTime
    expandedRowsComputableInPolyTime
    alignedFieldValuesComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

/-- The generic lookup machine emits all twelve selected fields per stable
source-pair representative in polynomial time. -/
noncomputable def selectedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields selectedFields := by
  exact LastTrueUnaryValueLookupMachine.afterComputableInPolyTime
    descriptorInputEncoding input inputComputableInPolyTime

end CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing

end
