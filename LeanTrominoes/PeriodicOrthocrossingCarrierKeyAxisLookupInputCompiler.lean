/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupInput
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisSentinelCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRepresentativeRowRecipeCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for retained carrier-key axis lookup inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Fork the representative-row and sentinel-completed axis compilers into
the exact separated encoding expected by the generic lookup machine. -/
noncomputable def inputComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      LastTrueUnaryValueLookupMachine.encode input := by
  let paired := TM2ForkMachine.computableInPolyTime
    paddedCarrierKeyRepresentativeRowsRecipeComputableInPolyTime
    paddedCarrierKeyAxisValuesWithSentinelComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing

end
