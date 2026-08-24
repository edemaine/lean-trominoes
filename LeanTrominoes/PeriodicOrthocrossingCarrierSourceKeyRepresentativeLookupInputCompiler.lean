/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupInput
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for compact carrier representative lookup inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Fork the compiled compact representative rows with any polynomial-time
aligned unary value stream. -/
noncomputable def inputComputableInPolyTime
    (alignedValues : List RouteDescriptor → List Nat)
    (alignedLength : ∀ descriptors,
      (alignedValues descriptors).length =
        (paddedCarrierSourceKeyCandidateStream descriptors).length + 1)
    (alignedValuesComputableInPolyTime :
      TM2ComputableInPolyTime
        (fun descriptors : List RouteDescriptor =>
          DelimitedBinaryWords.encode
            (RouteDescriptorBinaryWords.words descriptors))
        UnaryFieldEncoderMachine.unaryFields alignedValues) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      LastTrueUnaryValueLookupMachine.encode
      (input alignedValues alignedLength) := by
  let paired := TM2ForkMachine.computableInPolyTime
    paddedCarrierSourceKeyRepresentativeRowsComputableInPolyTime
    alignedValuesComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

end CarrierSourceKeyRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing

end
