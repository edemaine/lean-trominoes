/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecLiteralPrefix
import LeanTrominoes.PolyominoStripCycleSearch
import LeanTrominoes.Theorem55StripRawDecider

/-! # Insert the fixed tile into enriched strip input fields -/

namespace LeanTrominoes.Theorem55StripDecider.Evaluator
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open PolyominoStripWindow

def fields (input : Theorem55.StripInput) : List Nat := bound input :: Theorem55StripEncoding.fields input

def smallCoordinates : List Nat := Arithmetic.coordinates smallCells

def suffixCode : Code :=
  Code.prepend (Code.get 1) (Code.prepend (Code.get 0) (Code.prepend Code.zero (Code.prepend Code.zero
    (Code.prepend (Code.numeral 15) (Code.prepend (Code.get 2) (Code.prefixLiterals smallCoordinates (Code.drop 3)))))))

def suffixCoefficient : Nat :=
  4*(20000+4*(10000+4*(10000+4*(10000+4*(literalCoefficient 15+
    4*(30000+prefixCoefficient smallCoordinates 40000+1)+1)+1)+1)+1)+1)

theorem suffix_eval (input : Theorem55.StripInput) :
    suffixCode.eval (fields input) = pure (Savitch.suffix (rawCells input) input.1 (bound input)) := by
  have rest := Code.prefixLiterals_eval smallCoordinates (Code.drop 3) (fields input)
    ((fields input).drop 3) (by simp)
  simp only [suffixCode,Code.prepend_eval_eq,rest]
  simp [fields,Theorem55StripEncoding.fields,Savitch.suffix,Arithmetic.input,rawCells,smallCells,smallCoordinates,
    Arithmetic.coordinates]

theorem suffix_fits (input : Theorem55.StripInput) :
    EvaluatorCodeFits suffixCode (fields input) (Savitch.suffix (rawCells input) input.1 (bound input))
      (suffixCoefficient*(encodedListSpace (fields input)+1)) := by
  let values := fields input
  have hz : EvaluatorCodeFits Code.zero values [0] (10000*(encodedListSpace values+1)) :=
    (zero values).mono (listCodeZeroCost_le_linear values)
  have rest := prefixLiterals_linear smallCoordinates (drop_linear 3 values)
  have result := prepend_linear (get_linear 1 values) (prepend_linear (get_linear 0 values)
    (prepend_linear hz (prepend_linear hz (prepend_linear (literal_linear 15 values)
      (prepend_linear (get_linear 2 values) rest)))))
  change EvaluatorCodeFits suffixCode values (Savitch.suffix (rawCells input) input.1 (bound input))
    (suffixCoefficient*(encodedListSpace values+1)) at result
  exact result

theorem raw_bounded (input : Theorem55.StripInput) : Bounded (Raw.tiles (rawCells input)) (bound input) := by
  rw [rawCells_tiles]
  exact tiles_bounded input

end LeanTrominoes.Theorem55StripDecider.Evaluator
