import LeanTrominoes.PartrecDynamicDropSpace
import LeanTrominoes.PartrecFlatMotifIndex
import LeanTrominoes.PartrecMultiplySpace

/-!
# Evaluator-space certificate for dynamic flat motif indexing

The native motif indexer computes `headerLength + 2 * index`, dynamically
drops that prefix, and projects one of the next two coordinate fields.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def flatMotifIndexProductArgumentsCost
    (indexField : Nat) (values : List Nat) : Nat :=
  prependCost values [2] [values[indexField]?.getD 0]
    (numeralCost 2 values) (getCost indexField values)

theorem flatMotifIndexProductArguments
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.flatMotifIndexProductArgumentsCode indexField)
      values [2, values[indexField]?.getD 0]
      (flatMotifIndexProductArgumentsCost indexField values) := by
  simpa [Code.flatMotifIndexProductArgumentsCode,
    flatMotifIndexProductArgumentsCost, prependCost] using
    prepend (numeral 2 values) (get indexField values)

def flatMotifIndexProductCost
    (indexField : Nat) (values : List Nat) : Nat :=
  natMultiplyCost 2 (values[indexField]?.getD 0) +
    flatMotifIndexProductArgumentsCost indexField values

theorem flatMotifIndexProduct
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.flatMotifIndexProductCode indexField) values
      [2 * values[indexField]?.getD 0]
      (flatMotifIndexProductCost indexField values) := by
  simpa [Code.flatMotifIndexProductCode, flatMotifIndexProductCost] using
    comp (natMultiply 2 (values[indexField]?.getD 0))
      (flatMotifIndexProductArguments indexField values)

def flatMotifIndexOffsetCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  addConstCost headerLength [2 * values[indexField]?.getD 0] +
    flatMotifIndexProductCost indexField values

theorem flatMotifIndexOffset
    (headerLength indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.flatMotifIndexOffsetCode headerLength indexField) values
      [headerLength + 2 * values[indexField]?.getD 0]
      (flatMotifIndexOffsetCost headerLength indexField values) := by
  simpa [Code.flatMotifIndexOffsetCode, flatMotifIndexOffsetCost,
    Nat.add_comm] using
    comp (addConst headerLength [2 * values[indexField]?.getD 0])
      (flatMotifIndexProduct indexField values)

def flatMotifIndexDropInputCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  prependCost values [offset] values
    (flatMotifIndexOffsetCost headerLength indexField values) (idCost values)

theorem flatMotifIndexDropInput
    (headerLength indexField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifIndexDropInputCode headerLength indexField) values
      (offset :: values)
      (flatMotifIndexDropInputCost headerLength indexField values) := by
  simp only
  simpa [Code.flatMotifIndexDropInputCode,
    flatMotifIndexDropInputCost, prependCost] using
    prepend (flatMotifIndexOffset headerLength indexField values) (id values)

def flatMotifIndexedSuffixCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  dynamicDropCost offset values +
    flatMotifIndexDropInputCost headerLength indexField values

theorem flatMotifIndexedSuffix
    (headerLength indexField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifIndexedSuffixCode headerLength indexField) values
      (values.drop offset)
      (flatMotifIndexedSuffixCost headerLength indexField values) := by
  simp only
  let offset := headerLength + 2 * values[indexField]?.getD 0
  simpa [Code.flatMotifIndexedSuffixCode, flatMotifIndexedSuffixCost,
    offset] using
    comp (dynamicDrop offset values)
      (flatMotifIndexDropInput headerLength indexField values)

def flatMotifCellFieldAtCost
    (headerLength indexField outputField : Nat)
    (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  getCost outputField (values.drop offset) +
    flatMotifIndexedSuffixCost headerLength indexField values

theorem flatMotifCellFieldAt
    (headerLength indexField outputField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifCellFieldAtCode headerLength indexField outputField)
      values [(values.drop offset)[outputField]?.getD 0]
      (flatMotifCellFieldAtCost headerLength indexField outputField values) := by
  simp only
  let offset := headerLength + 2 * values[indexField]?.getD 0
  simpa [Code.flatMotifCellFieldAtCode, flatMotifCellFieldAtCost, offset] using
    comp (get outputField (values.drop offset))
      (flatMotifIndexedSuffix headerLength indexField values)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
