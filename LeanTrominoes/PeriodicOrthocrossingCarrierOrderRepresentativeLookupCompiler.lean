/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupInputCompiler

/-! # Compiler for representative carrier order coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeLookup

open Computability Turing

/-- Representative lookup emits every selected positive or negative carrier
order coordinate in polynomial time. -/
noncomputable def valuesComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values keepPositive) := by
  exact LastTrueUnaryValueLookupMachine.afterComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    (input keepPositive)
    (inputComputableInPolyTime keepPositive)

end CarrierOrderRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing

end
