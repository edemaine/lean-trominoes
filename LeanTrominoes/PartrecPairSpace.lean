import LeanTrominoes.PartrecPair
import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecMultiplySpace
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space composition for forward pairing

This file fits the explicit squares, sums, and strict-comparison branch used
by `natPairCode`.  The certificate is continuation-independent and exposes
the exact cost of the branch selected by the defining equation of `Nat.pair`.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def natPairLeftSquareArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left] [left]
    (getCost 0 [left, right]) (getCost 0 [left, right])

theorem natPairLeftSquareArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairLeftSquareArgumentsCode
      [left, right] [left, left]
      (natPairLeftSquareArgumentsCost left right) := by
  simpa [Code.natPairLeftSquareArgumentsCode,
    natPairLeftSquareArgumentsCost, prependCost] using
    prepend (get 0 [left, right]) (get 0 [left, right])

def natPairRightSquareArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [right] [right]
    (getCost 1 [left, right]) (getCost 1 [left, right])

theorem natPairRightSquareArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairRightSquareArgumentsCode
      [left, right] [right, right]
      (natPairRightSquareArgumentsCost left right) := by
  simpa [Code.natPairRightSquareArgumentsCode,
    natPairRightSquareArgumentsCost, prependCost] using
    prepend (get 1 [left, right]) (get 1 [left, right])

def natPairLeftSquareCost (left right : Nat) : Nat :=
  natMultiplyCost left left +
    natPairLeftSquareArgumentsCost left right

theorem natPairLeftSquare (left right : Nat) :
    EvaluatorCodeFits Code.natPairLeftSquareCode
      [left, right] [left * left]
      (natPairLeftSquareCost left right) := by
  simpa [Code.natPairLeftSquareCode,
    natPairLeftSquareCost] using
    comp (natMultiply left left)
      (natPairLeftSquareArguments left right)

def natPairRightSquareCost (left right : Nat) : Nat :=
  natMultiplyCost right right +
    natPairRightSquareArgumentsCost left right

theorem natPairRightSquare (left right : Nat) :
    EvaluatorCodeFits Code.natPairRightSquareCode
      [left, right] [right * right]
      (natPairRightSquareCost left right) := by
  simpa [Code.natPairRightSquareCode,
    natPairRightSquareCost] using
    comp (natMultiply right right)
      (natPairRightSquareArguments left right)

def natPairLowerArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [right * right] [left]
    (natPairRightSquareCost left right)
    (getCost 0 [left, right])

theorem natPairLowerArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairLowerArgumentsCode
      [left, right] [right * right, left]
      (natPairLowerArgumentsCost left right) := by
  simpa [Code.natPairLowerArgumentsCode,
    natPairLowerArgumentsCost, prependCost] using
    prepend (natPairRightSquare left right)
      (get 0 [left, right])

def natPairLowerCost (left right : Nat) : Nat :=
  natAddCost (right * right) left +
    natPairLowerArgumentsCost left right

theorem natPairLower (left right : Nat) :
    EvaluatorCodeFits Code.natPairLowerCode
      [left, right] [right * right + left]
      (natPairLowerCost left right) := by
  simpa [Code.natPairLowerCode, natPairLowerCost] using
    comp (natAdd (right * right) left)
      (natPairLowerArguments left right)

def natPairUpperFirstArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left * left] [left]
    (natPairLeftSquareCost left right)
    (getCost 0 [left, right])

theorem natPairUpperFirstArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperFirstArgumentsCode
      [left, right] [left * left, left]
      (natPairUpperFirstArgumentsCost left right) := by
  simpa [Code.natPairUpperFirstArgumentsCode,
    natPairUpperFirstArgumentsCost, prependCost] using
    prepend (natPairLeftSquare left right)
      (get 0 [left, right])

def natPairUpperFirstCost (left right : Nat) : Nat :=
  natAddCost (left * left) left +
    natPairUpperFirstArgumentsCost left right

theorem natPairUpperFirst (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperFirstCode
      [left, right] [left * left + left]
      (natPairUpperFirstCost left right) := by
  simpa [Code.natPairUpperFirstCode,
    natPairUpperFirstCost] using
    comp (natAdd (left * left) left)
      (natPairUpperFirstArguments left right)

def natPairUpperArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left * left + left] [right]
    (natPairUpperFirstCost left right)
    (getCost 1 [left, right])

theorem natPairUpperArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperArgumentsCode
      [left, right] [left * left + left, right]
      (natPairUpperArgumentsCost left right) := by
  simpa [Code.natPairUpperArgumentsCode,
    natPairUpperArgumentsCost, prependCost] using
    prepend (natPairUpperFirst left right)
      (get 1 [left, right])

def natPairUpperCost (left right : Nat) : Nat :=
  natAddCost (left * left + left) right +
    natPairUpperArgumentsCost left right

theorem natPairUpper (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperCode
      [left, right] [left * left + left + right]
      (natPairUpperCost left right) := by
  simpa [Code.natPairUpperCode, natPairUpperCost] using
    comp (natAdd (left * left + left) right)
      (natPairUpperArguments left right)

def natPairCost (left right : Nat) : Nat :=
  if left < right then
    branchZeroSuccCost [left, right] [Nat.pair left right]
      1 (natLtCost left right) (natPairLowerCost left right)
  else
    branchZeroZeroCost [left, right] [Nat.pair left right]
      0 (natLtCost left right) (natPairUpperCost left right)

/-- Exact fitted certificate for the standard forward pairing program. -/
theorem natPair (left right : Nat) :
    EvaluatorCodeFits Code.natPairCode
      [left, right] [Nat.pair left right]
      (natPairCost left right) := by
  by_cases less : left < right
  · have testFit :
        EvaluatorCodeFits Code.natLtCode [left, right] [1]
          (natLtCost left right) := by
        simpa [less] using natLt left right
    have branch := branchZero_succ
      (whenZero := Code.natPairUpperCode)
      (show 0 < 1 by omega)
      testFit (natPairLower left right)
    simpa [Code.natPairCode, natPairCost,
      Nat.pair, less] using branch
  · have testFit :
        EvaluatorCodeFits Code.natLtCode [left, right] [0]
          (natLtCost left right) := by
        simpa [less] using natLt left right
    have branch := branchZero_zero
      (whenSucc := Code.natPairLowerCode) rfl
      testFit (natPairUpper left right)
    simpa [Code.natPairCode, natPairCost,
      Nat.pair, less] using branch

end EvaluatorCodeFits

end PartrecToTM2
end Turing
