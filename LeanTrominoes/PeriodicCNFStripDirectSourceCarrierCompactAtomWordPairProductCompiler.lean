/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordStreamCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordStreamNumericSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct compiler for the compact carrier-word ordered product -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairProductStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact globally ranked compact carrier words have a typed
delimiter encoding computable in polynomial time. -/
noncomputable def directSourceCarrierCompactAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token id
      DelimitedBinaryWords.finEncoding.encode
      (directSourceCarrierCompactAtomWords decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceCarrierCompactAtomWordTokensComputableInPolyTime decider)
    fun symbols => by
      simpa only [id_eq, DelimitedBinaryWords.finEncoding,
        directSourceCarrierCompactAtomWords] using
        directSourceCarrierCompactAtomWordTokens_eq_encode decider symbols

/-- The row-major square of globally ranked compact carrier words is
computable in polynomial time. -/
noncomputable def directSourceCarrierCompactAtomWordPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.finEncoding.encode
      (directSourceCarrierCompactAtomWordPairs decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWordPairs.Input
    encoding.Γ DelimitedBinaryWordPairs.Token id
    DelimitedBinaryWordPairs.finEncoding.encode
    (fun symbols => DelimitedBinaryWordPairProductMachine.pairs
      (directSourceCarrierCompactAtomWords decider symbols))
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierCompactAtomWordsComputableInPolyTime decider)
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
