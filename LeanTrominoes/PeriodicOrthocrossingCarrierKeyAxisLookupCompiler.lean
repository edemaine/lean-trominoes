/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupInputCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time retained carrier-key axis lookup -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

open Computability Turing

/-- The selected axis value of every carrier-key representative row is
emitted as a unary field in polynomial time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields values := by
  let lookedUp := TM2CompositionMachine.computableInPolyTime
    inputComputableInPolyTime
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq lookedUp
    (fun _ => by rfl)

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing

end
