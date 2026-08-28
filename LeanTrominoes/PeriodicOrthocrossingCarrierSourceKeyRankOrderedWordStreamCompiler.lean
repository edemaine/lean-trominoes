/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Globally rank-ordered physical carrier source-pair words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedWordStream

open Computability Turing

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  CarrierSourceKeyRankOrderedFields.descriptorInputEncoding

/-- Reconstruct one guarded physical source-pair word for every globally
ranked carrier datum. -/
def emittedTokens (descriptors : List RouteDescriptor) :
    List DelimitedBinaryWords.Token :=
  CarrierSourcePairFieldFormatter.output
    (UnaryFieldEncoderMachine.unaryFields
      (CarrierSourceKeyRankOrderedFields.values descriptors))

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id emittedTokens := by
  let formatter : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun values => CarrierSourcePairFieldFormatter.output
        (UnaryFieldEncoderMachine.unaryFields values)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields
      CarrierSourcePairFieldFormatter.computableInPolyTime
      (fun _ => rfl) (fun _ => rfl)
  let composed : TM2ComputableInPolyTime descriptorInputEncoding id
      (fun descriptors => CarrierSourcePairFieldFormatter.output
        (UnaryFieldEncoderMachine.unaryFields
          (CarrierSourceKeyRankOrderedFields.values descriptors))) :=
    TM2CompositionMachine.computableInPolyTime
      (A := List RouteDescriptor) (B := List Nat)
      (C := List DelimitedBinaryWords.Token)
      (encodeA := descriptorInputEncoding)
      (encodeB := UnaryFieldEncoderMachine.unaryFields)
      (encodeC := id)
      (f := CarrierSourceKeyRankOrderedFields.values)
      (g := fun values => CarrierSourcePairFieldFormatter.output
        (UnaryFieldEncoderMachine.unaryFields values))
      CarrierSourceKeyRankOrderedFields.valuesComputableInPolyTime formatter
  exact composed

end CarrierSourceKeyRankOrderedWordStream
end LeanTrominoes.PeriodicOrthocrossing

end
