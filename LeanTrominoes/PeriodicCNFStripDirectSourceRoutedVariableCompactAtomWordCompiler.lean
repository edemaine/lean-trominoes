/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedVariableCompactAtomWordSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct compiler for routed-variable compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedVariableCompactCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def directSourceRoutedVariableCompactAtomWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token
      id id (directSourceRoutedVariableCompactAtomWordTokens decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List DelimitedBinaryWords.Token)
    encoding.Γ DelimitedBinaryWords.Token id id
    (fun symbols => RoutedVariableCompactAtomWordStream.emittedStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider)
    RoutedVariableCompactAtomWordStream.emittedStreamComputableInPolyTime

/-- Direct source symbols compile to the complete routed-variable pair-scan
word stream in polynomial time. -/
noncomputable def directSourceRoutedVariableCompactAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceRoutedVariableCompactAtomWords decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceRoutedVariableCompactAtomWordTokensComputableInPolyTime decider)
    fun symbols => by
      simpa only [id_eq, DelimitedBinaryWords.finEncoding] using
        directSourceRoutedVariableCompactAtomWordTokens_eq_encode
          decider symbols

/-- Direct source symbols compile to the exact final five-family
routed-variable compact atom-word block in polynomial time. -/
noncomputable def
    directSourceFinalRoutedVariableCompactAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalRoutedVariableCompactAtomWords decider) := by
  have functionEq :
      directSourceRoutedVariableCompactAtomWords decider =
        directSourceFinalRoutedVariableCompactAtomWords decider := by
    funext symbols
    exact directSourceRoutedVariableCompactAtomWords_eq_final
      decider symbols
  rw [← functionEq]
  exact directSourceRoutedVariableCompactAtomWordsComputableInPolyTime decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
