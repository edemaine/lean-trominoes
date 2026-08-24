/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotSemanticCompiler
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for the ordered square of fixed occurrence-slot words -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

open Computability Turing

/-- Expand every input word into fixed occurrence slots, then form the
row-major square of the expanded word list. -/
def expandedPairs (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs (expandInput input)

/-- The exact ordered square of the eighty-one-copy expansion is
polynomial-time computable. -/
noncomputable def expandedPairsComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWordPairs.finEncoding.encode expandedPairs := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode
    DelimitedBinaryWordPairs.finEncoding.encode
    (fun input => DelimitedBinaryWordPairProductMachine.pairs
      (expandInput input))
  exact TM2CompositionMachine.computableInPolyTime
    expandInputComputableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes

end
