/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time row structure for promised-source atom equalities -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomEqualityRows

open Computability Turing
open SourceOccurrenceAtomEqualities

def occurrenceCount
    (source : SourceSplitRouteDescriptorTokens.Source) : Nat :=
  (PeriodicThreeSATThree.taggedLiterals source.formula).length

@[simp] theorem atomEqualityMatrix_length (formula : PeriodicCNF Nat) :
    (SourceOccurrenceAtomPairs.atomEqualityMatrix formula).length =
      (PeriodicThreeSATThree.taggedLiterals formula).length ^ 2 := by
  simp [SourceOccurrenceAtomPairs.atomEqualityMatrix, pow_two]

@[simp] theorem sourceAtomEqualityMatrix_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceAtomEqualityMatrix source).length = occurrenceCount source ^ 2 := by
  simp [sourceAtomEqualityMatrix, occurrenceCount]

/-- The flat equality list equipped with its canonical square-length proof. -/
def squareInput
    (source : SourceSplitRouteDescriptorTokens.Source) :
    BoolSquareRows.Input where
  bits := sourceAtomEqualityMatrix source
  square := by
    rw [sourceAtomEqualityMatrix_length, Nat.sqrt_eq']

/-- Equality rows in stable literal-occurrence order. -/
def rows (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.Input :=
  (squareInput source).delimitedRows

/-- Reinterpret the established flat equality compiler at the promised-square
semantic type without changing its physical Boolean output. -/
noncomputable def squareInputComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source BoolSquareRows.Input
      PeriodicCNFFlatEncoding.Symbol Bool
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      BoolSquareRows.finEncoding.encode squareInput := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    sourceAtomEqualityMatrixComputableInPolyTime (fun _ => rfl)

/-- Parsing a promised source, comparing every ordered occurrence pair, and
recovering the equality-matrix row boundaries is polynomial time. -/
noncomputable def rowsComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source DelimitedBinaryWords.Input
      PeriodicCNFFlatEncoding.Symbol DelimitedBinaryWords.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode rows := by
  let composed := TM2CompositionMachine.computableInPolyTime
    squareInputComputableInPolyTime
    BoolSquareRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end SourceOccurrenceAtomEqualityRows
end PeriodicCNF
end LeanTrominoes

end
