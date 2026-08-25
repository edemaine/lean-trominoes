/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerAdditionCompiler
import LeanTrominoes.UnaryAlignedAddTime

/-! # Polynomial-time stable lower carrier ranks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

/-- Stable, presentation-tie-broken lower ranks for all compact carrier data
are computable in polynomial time. -/
opaque ranksComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields ranks := by
  let added := TM2CompositionMachine.computableInPolyTime
    additionInputComputableInPolyTime
    UnaryAlignedAddMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := ranks) added (fun input => by
      simp only [ranks, additionInput])

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end
