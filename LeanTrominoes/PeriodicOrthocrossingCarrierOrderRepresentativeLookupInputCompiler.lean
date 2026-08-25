/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupInput
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for carrier order-coordinate lookup inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Fork the compiled representative rows with the aligned sentinel-extended
positive or negative order-coordinate stream. -/
noncomputable def inputComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      LastTrueUnaryValueLookupMachine.encode
      (input keepPositive) := by
  let paired := TM2ForkMachine.computableInPolyTime
    CarrierOrderRepresentativeRows.rowsComputableInPolyTime
    (CarrierOrderCandidateFieldStream.valuesWithSentinelComputableInPolyTime
      keepPositive)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

end CarrierOrderRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing

end
