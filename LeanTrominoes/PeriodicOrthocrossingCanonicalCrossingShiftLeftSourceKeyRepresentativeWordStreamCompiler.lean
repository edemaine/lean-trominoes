/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for representative canonical crossing source-pair words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream

open Computability Turing

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.descriptorInputEncoding

/-- Reconstruct guarded source-pair words from the selected twelve-field
blocks. -/
def emittedTokens (descriptors : List RouteDescriptor) :
    List DelimitedBinaryWords.Token :=
  CarrierSourcePairFieldFormatter.output
    (UnaryFieldEncoderMachine.unaryFields
      (CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.selectedFields
        descriptors))

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id emittedTokens := by
  change TM2ComputableInPolyTime descriptorInputEncoding id
    (fun descriptors => CarrierSourcePairFieldFormatter.output
      (UnaryFieldEncoderMachine.unaryFields
        (CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.selectedFields
          descriptors)))
  let fields : TM2ComputableInPolyTime descriptorInputEncoding id
      (fun descriptors => UnaryFieldEncoderMachine.unaryFields
        (CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.selectedFields
          descriptors)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.selectedFieldsComputableInPolyTime
      (fun _ => rfl)
  exact TM2CompositionMachine.computableInPolyTime fields
    CarrierSourcePairFieldFormatter.computableInPolyTime

end CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream
end LeanTrominoes.PeriodicOrthocrossing

end
