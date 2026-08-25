/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerCountCompiler
import LeanTrominoes.TM2ForkMachineTime

/-! # Compiler preparation for stable carrier-rank addition -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

opaque additionInputComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryAlignedAddMachine.encode additionInput := by
  let paired := TM2ForkMachine.computableInPolyTime
    lowerCountsComputableInPolyTime tieCountsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun input => by
      simp only [UnaryAlignedAddMachine.encode, additionInput])

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end
