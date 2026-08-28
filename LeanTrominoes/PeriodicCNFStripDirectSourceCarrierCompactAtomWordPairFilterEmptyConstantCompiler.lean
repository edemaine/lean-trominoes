/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairData
import LeanTrominoes.TM2ConstantValueCompiler

/-! # Constant carrier-pair output at the empty source word -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierPairEmptyConstantStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierPairEmptyConstantTokenInhabited :
    Inhabited DelimitedBinaryWordPairs.Token :=
  ⟨.pairStart⟩

noncomputable def
    directSourceCarrierSelectedCompactAtomWordPairsAtNilComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.encode
      (fun _ => directSourceCarrierSelectedCompactAtomWordPairs decider []) := by
  exact TM2ConstantValueCompiler.computableInPolyTime
    (Input := List encoding.Γ) id DelimitedBinaryWordPairs.encode
    (directSourceCarrierSelectedCompactAtomWordPairs decider [])

end PeriodicCNFStripReduction
end LeanTrominoes

end
