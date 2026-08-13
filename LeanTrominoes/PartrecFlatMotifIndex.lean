import LeanTrominoes.PartrecDynamicDrop
import LeanTrominoes.PartrecMultiply
import LeanTrominoes.PeriodicStripFlatEncoding

/-!
# Dynamic indexing into flat motif coordinates

Motif-wide transition checks must retain the complete coordinate stream for
nested assignment lookups.  Rather than consume that stream, this module
computes `header length + 2 * motif index`, drops that many native fields, and
selects one of the leading cell coordinates.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Assemble `[2, motifIndex]`. -/
def flatMotifIndexProductArgumentsCode (indexField : Nat) : Code :=
  prepend (numeral 2) (get indexField)

/-- Compute twice the motif index. -/
def flatMotifIndexProductCode (indexField : Nat) : Code :=
  natMultiplyCode.comp (flatMotifIndexProductArgumentsCode indexField)

/-- Compute the native-field offset of the selected motif cell. -/
def flatMotifIndexOffsetCode
    (headerLength indexField : Nat) : Code :=
  (addConst headerLength).comp (flatMotifIndexProductCode indexField)

@[simp]
theorem flatMotifIndexOffsetCode_eval
    (headerLength indexField : Nat) (values : List Nat) :
    (flatMotifIndexOffsetCode headerLength indexField).eval values =
      pure [headerLength + 2 * values[indexField]?.getD 0] := by
  simp [flatMotifIndexOffsetCode, flatMotifIndexProductCode,
    flatMotifIndexProductArgumentsCode]
  omega

/-- Prepend the dynamic offset to the untouched payload. -/
def flatMotifIndexDropInputCode
    (headerLength indexField : Nat) : Code :=
  prepend (flatMotifIndexOffsetCode headerLength indexField) id

@[simp]
theorem flatMotifIndexDropInputCode_eval
    (headerLength indexField : Nat) (values : List Nat) :
    (flatMotifIndexDropInputCode headerLength indexField).eval values =
      pure
        ((headerLength + 2 * values[indexField]?.getD 0) :: values) := by
  simp [flatMotifIndexDropInputCode]

/-- Suffix beginning at the selected motif cell. -/
def flatMotifIndexedSuffixCode
    (headerLength indexField : Nat) : Code :=
  dynamicDropCode.comp
    (flatMotifIndexDropInputCode headerLength indexField)

@[simp]
theorem flatMotifIndexedSuffixCode_eval
    (headerLength indexField : Nat) (values : List Nat) :
    (flatMotifIndexedSuffixCode headerLength indexField).eval values =
      pure
        (values.drop
          (headerLength + 2 * values[indexField]?.getD 0)) := by
  calc
    _ = dynamicDropCode.eval
        ((headerLength + 2 * values[indexField]?.getD 0) :: values) :=
      comp_eval_pure _ _ _ _
        (flatMotifIndexDropInputCode_eval
          headerLength indexField values)
    _ = _ := dynamicDropCode_eval _ _

/-- Select coordinate field zero or one of the indexed motif cell. -/
def flatMotifCellFieldAtCode
    (headerLength indexField outputField : Nat) : Code :=
  (get outputField).comp
    (flatMotifIndexedSuffixCode headerLength indexField)

@[simp]
theorem flatMotifCellFieldAtCode_eval
    (headerLength indexField outputField : Nat) (values : List Nat) :
    (flatMotifCellFieldAtCode
      headerLength indexField outputField).eval values =
      pure
        [(values.drop
          (headerLength + 2 * values[indexField]?.getD 0))[outputField]?.getD 0] := by
  calc
    _ = (get outputField).eval
        (values.drop
          (headerLength + 2 * values[indexField]?.getD 0)) :=
      comp_eval_pure _ _ _ _
        (flatMotifIndexedSuffixCode_eval
          headerLength indexField values)
    _ = _ := by simp

theorem flatMotifCoordinates_drop_processed
    (processed : List Cell) (cell : Cell) (remaining : List Cell) :
    ((processed ++ cell :: remaining).flatMap
      PeriodicStripFlatEncoding.cellFields).drop
        (2 * processed.length) =
      PeriodicStripFlatEncoding.cellFields cell ++
        remaining.flatMap PeriodicStripFlatEncoding.cellFields := by
  induction processed with
  | nil => simp
  | cons head processed induction =>
      rcases head with ⟨headX, headY⟩
      simp [PeriodicStripFlatEncoding.cellFields] at induction ⊢
      simpa [Nat.mul_succ] using induction

@[simp]
theorem flatMotifCoordinates_length (motif : List Cell) :
    (motif.flatMap PeriodicStripFlatEncoding.cellFields).length =
      2 * motif.length := by
  induction motif with
  | nil => rfl
  | cons cell motif induction =>
      rcases cell with ⟨x, y⟩
      simp [PeriodicStripFlatEncoding.cellFields, induction]
      omega

/-- The transition scanners use nine scalar fields, with the processed-cell
count in field one.  On a semantic split of the motif, indexed selection
returns the requested coordinate of the next cell. -/
@[simp]
theorem flatMotifCellFieldAtCode_eval_nineHeader
    (valid a2 a3 a4 a5 a6 a7 a8 : Nat) (outputField : Fin 2)
    (processed : List Cell) (cell : Cell) (remaining : List Cell) :
    (flatMotifCellFieldAtCode 9 1 outputField).eval
        ([valid, processed.length, a2, a3, a4, a5, a6, a7, a8] ++
          (processed ++ cell :: remaining).flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(PeriodicStripFlatEncoding.cellFields cell)[outputField.val]?.getD 0] := by
  rw [flatMotifCellFieldAtCode_eval]
  have indexValue :
      ([valid, processed.length, a2, a3, a4, a5, a6, a7, a8] ++
        (processed ++ cell :: remaining).flatMap
          PeriodicStripFlatEncoding.cellFields)[1]?.getD 0 =
        processed.length := by simp
  rw [indexValue]
  rw [List.flatMap_append]
  simp only [List.flatMap_cons]
  simp only [List.getElem?_drop]
  congr 2
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [List.getElem?_append_right (by
    rw [flatMotifCoordinates_length]
    omega)]
  rw [List.getElem?_append_left (by
    rcases cell with ⟨x, y⟩
    simp [PeriodicStripFlatEncoding.cellFields]
    have := outputField.isLt
    omega)]
  congr 2
  rw [flatMotifCoordinates_length]
  omega

end Turing.ToPartrec.Code
