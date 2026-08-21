/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListSplitLengthsFlatMapFixed
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowCompiler

/-! # Semantics of source occurrence atom-equality rows -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomEqualityRows

/-- The explicit atom-equality row belonging to every literal occurrence. -/
def semanticRows (formula : PeriodicCNF Nat) : List (List Bool) :=
  (PeriodicThreeSATThree.taggedLiterals formula).map fun first =>
    (PeriodicThreeSATThree.taggedLiterals formula).map fun second =>
      decide (first.1.atom = second.1.atom)

@[simp] theorem squareInput_side
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (squareInput source).side = occurrenceCount source := by
  unfold BoolSquareRows.Input.side squareInput
  rw [sourceAtomEqualityMatrix_length, Nat.sqrt_eq']

/-- Square-row recovery preserves the presentation order and gives exactly
the explicit equality row for each source literal occurrence. -/
theorem rows_words
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (rows source).words = semanticRows source.formula := by
  unfold rows BoolSquareRows.Input.delimitedRows BoolSquareRows.Input.rows
    BoolSquareRows.Input.sizes
  rw [squareInput_side]
  unfold squareInput SourceOccurrenceAtomEqualities.sourceAtomEqualityMatrix
    SourceOccurrenceAtomPairs.atomEqualityMatrix semanticRows
  exact List.replicate_splitLengths_flatMap_of_length_eq
    (PeriodicThreeSATThree.taggedLiterals source.formula)
    (fun first =>
      (PeriodicThreeSATThree.taggedLiterals source.formula).map fun second =>
        decide (first.1.atom = second.1.atom))
    (PeriodicThreeSATThree.taggedLiterals source.formula).length
    (by intro; simp)

end SourceOccurrenceAtomEqualityRows
end PeriodicCNF
end LeanTrominoes
