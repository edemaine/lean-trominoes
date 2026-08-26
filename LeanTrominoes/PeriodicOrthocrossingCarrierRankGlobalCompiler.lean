/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyBlockStartCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryAlignedAddTime

/-! # Compiler for global key-major stable carrier ranks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

open Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

opaque additionInputComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryAlignedAddMachine.encode additionInput := by
  let paired := TM2ForkMachine.computableInPolyTime
    CarrierRankKeyBlockStarts.unaryFieldsComputableInPolyTime
    CarrierRankStableLower.ranksComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun descriptors => by
      simp only [UnaryAlignedAddMachine.encode, additionInput])

/-- Global key-major ranks of all compact carrier data are emitted in unary
in polynomial time. -/
opaque ranksComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields ranks := by
  let added := TM2CompositionMachine.computableInPolyTime
    additionInputComputableInPolyTime
    UnaryAlignedAddMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq added
    (fun descriptors => by
      simp only [ranks, additionInput])

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing

end
