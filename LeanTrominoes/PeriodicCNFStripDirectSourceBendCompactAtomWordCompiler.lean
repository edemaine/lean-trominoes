/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct compiler for compact retained-bend atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceBendCompactCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def directSourceBendCompactAtomWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token
      id id (directSourceBendCompactAtomWordTokens decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List DelimitedBinaryWords.Token)
    encoding.Γ DelimitedBinaryWords.Token id id
    (fun symbols => BendCompactAtomWordStream.emittedStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider)
    BendCompactAtomWordStream.emittedStreamComputableInPolyTime

/-- Direct PSPACE source symbols compile to the complete exact base-bend
compact occurrence-word stream in polynomial time. -/
noncomputable def directSourceBendCompactAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceBendCompactAtomWords decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceBendCompactAtomWordTokensComputableInPolyTime decider)
    fun symbols => by
      simpa only [id_eq, DelimitedBinaryWords.finEncoding] using
        directSourceBendCompactAtomWordTokens_eq_encode decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
