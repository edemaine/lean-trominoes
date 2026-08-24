/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupInputCompiler

/-! # Compiler for lookup through compact carrier representatives -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeLookup

open Computability Turing

/-- Representative lookup preserves polynomial time for every exactly aligned
unary value compiler. -/
noncomputable def valuesComputableInPolyTime
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
      UnaryFieldEncoderMachine.unaryFields
      (values alignedValues) :=
  LastTrueUnaryValueLookupMachine.afterComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    (input alignedValues alignedLength)
    (inputComputableInPolyTime
      alignedValues alignedLength alignedValuesComputableInPolyTime)

end CarrierSourceKeyRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing

end
