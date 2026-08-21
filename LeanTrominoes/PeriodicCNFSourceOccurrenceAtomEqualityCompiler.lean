/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomWordCompiler
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.DelimitedBinaryWordPairEqualityTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time atom-equality matrices for promised sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomEqualities

open Computability Turing

/-- Row-major equality bits for the literal occurrences of one promised
source. -/
def sourceAtomEqualityMatrix
    (source : SourceSplitRouteDescriptorTokens.Source) : List Bool :=
  SourceOccurrenceAtomPairs.atomEqualityMatrix source.formula

theorem pairs_sourceWords
    (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWordPairProductMachine.pairs
        (SourceOccurrenceAtomWords.sourceWords source) =
      SourceOccurrenceAtomPairs.input source.formula := by
  rfl

theorem equalities_pairs_sourceWords
    (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWordPairs.equalities
        (DelimitedBinaryWordPairProductMachine.pairs
          (SourceOccurrenceAtomWords.sourceWords source)) =
      sourceAtomEqualityMatrix source := by
  rw [pairs_sourceWords]
  exact SourceOccurrenceAtomPairs.equalities_input source.formula

/-- Parsing a promised source, enumerating every ordered occurrence pair,
and comparing its atom words is polynomial time. -/
noncomputable def sourceAtomEqualityMatrixComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source (List Bool)
      PeriodicCNFFlatEncoding.Symbol Bool
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      sourceAtomEqualityMatrix := by
  let paired := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomWords.sourceWordsComputableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let compared := TM2CompositionMachine.computableInPolyTime paired
    DelimitedBinaryWordPairEqualityMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compared
    equalities_pairs_sourceWords

end SourceOccurrenceAtomEqualities
end PeriodicCNF
end LeanTrominoes

end
