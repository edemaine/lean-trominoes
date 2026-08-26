/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyBlockStartData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyContributionStartCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for per-occurrence carrier-key block starts -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyBlockStarts

open Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

opaque unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankKeyEquality.InputEncoding
      UnaryFieldEncoderMachine.unaryFields starts := by
  let paired := TM2ForkMachine.computableInPolyTime
    CarrierRankKeyEqualityRows.rowsComputableInPolyTime
    CarrierRankKeyContributionStarts.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      CarrierRankKeyEquality.InputEncoding
      LastTrueUnaryValueLookupMachine.encode lookupInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun descriptors => by
        simp only [LastTrueUnaryValueLookupMachine.encode, lookupInput]
        rw [CarrierRankKeyEqualityRows.rows_eq_semanticRows]
        rfl)
  let lookedUp := TM2CompositionMachine.computableInPolyTime prepared
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq lookedUp
    (fun descriptors => by
      simp only [starts, lookupInput])

end CarrierRankKeyBlockStarts
end LeanTrominoes.PeriodicOrthocrossing

end
