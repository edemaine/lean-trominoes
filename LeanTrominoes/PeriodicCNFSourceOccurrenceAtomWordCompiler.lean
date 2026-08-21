/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomWordSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenCompilerSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time extraction of promised-source atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomWords

open Computability Turing

noncomputable def tokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List SourceOccurrenceTokens.Token)
      (List DelimitedBinaryWords.Token)
      SourceOccurrenceTokens.Token DelimitedBinaryWords.Token
      id id tokens :=
  FiniteBlockTransducer.computableInPolyTime block

/-- Semantic word-list output for one promised flat source. -/
def sourceWords (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.Input :=
  ⟨SourceOccurrenceAtomPairs.occurrenceAtomWords source.formula⟩

theorem encoded_sourceWords
    (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.finEncoding.encode (sourceWords source) =
      tokens (SourceOccurrenceTokens.formulaTokens source.formula) := by
  rw [tokens_formulaTokens]
  rfl

/-- Parsing a promised source and retaining only its atom subwords is
polynomial time. -/
noncomputable def sourceWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source DelimitedBinaryWords.Input
      PeriodicCNFFlatEncoding.Symbol DelimitedBinaryWords.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode sourceWords := by
  let physical := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceTokens.formulaTokensComputableInPolyTime
    tokensComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    fun source => by
      symm
      exact encoded_sourceWords source

end SourceOccurrenceAtomWords
end PeriodicCNF
end LeanTrominoes

end
