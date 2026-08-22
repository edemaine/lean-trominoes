/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorWordPairData
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for ordered route-descriptor word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorWordPairCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The complete ordered product of direct-source descriptor words is
computable in polynomial time. -/
noncomputable def directSourceRouteDescriptorWordPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token
      id DelimitedBinaryWordPairs.finEncoding.encode
      (fun symbols =>
        directSourceRouteDescriptorWordPairs decider symbols) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorBinaryWordsComputableInPolyTime decider)
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
  simpa only [directSourceRouteDescriptorWordPairs] using composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
