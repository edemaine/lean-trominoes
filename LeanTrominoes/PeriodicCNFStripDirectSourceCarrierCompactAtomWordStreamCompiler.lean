/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordStreamData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for direct-source compact carrier atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactAtomWordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct source symbols compile to one exact compact carrier atom word per
global carrier rank in polynomial time. -/
noncomputable def
    directSourceCarrierCompactAtomWordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierCompactAtomWordTokens decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (A := List encoding.Γ)
    (B := List DelimitedBinaryWords.Token)
    (C := List DelimitedBinaryWords.Token)
    (encodeA := id) (encodeB := id) (encodeC := id)
    (f := directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens decider)
    (g := GuardedCarrierSourcePairCompactAtomWords.tokens)
    (directSourceCarrierNormalizedSourceKeyRankOrderedWordTokensComputableInPolyTime
      decider)
    GuardedCarrierSourcePairCompactAtomWords.tokensComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols => GuardedCarrierSourcePairCompactAtomWords.tokens
      (directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
        decider symbols))
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
