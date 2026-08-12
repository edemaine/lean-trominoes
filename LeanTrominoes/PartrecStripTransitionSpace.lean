import LeanTrominoes.PartrecPackedTransitionSpace
import LeanTrominoes.PartrecStripFrontierContextSpace
import LeanTrominoes.PartrecStripTransition

/-!
# Evaluator-space certificate for the indexed strip transition

The fitted strip-context decoder feeds the fitted packed transition through
one fixed-width field permutation.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def stripPackedTransitionArgumentsCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  let values :=
    [periodicStrip.width, periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
  let nextFields := prependCost values
    [last % periodicStrip.period]
    [last / periodicStrip.period]
    (getCost 6 values) (getCost 5 values)
  let currentWord := prependCost values
    [first / periodicStrip.period]
    [last % periodicStrip.period, last / periodicStrip.period]
    (getCost 3 values) nextFields
  let motif := prependCost values
    [Encodable.encode periodicStrip.motif]
    [first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 2 values) currentWord
  let currentPhase := prependCost values
    [first % periodicStrip.period]
    [Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 4 values) motif
  prependCost values [periodicStrip.period]
    [first % periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 1 values) currentPhase

theorem stripPackedTransitionArguments
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripPackedTransitionArgumentsCode
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      [periodicStrip.period, first % periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        last % periodicStrip.period,
        last / periodicStrip.period]
      (stripPackedTransitionArgumentsCost
        periodicStrip first last) := by
  let values :=
    [periodicStrip.width, periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
  have nextFields := prepend (get 6 values) (get 5 values)
  have currentWord := prepend (get 3 values) nextFields
  have motif := prepend (get 2 values) currentWord
  have currentPhase := prepend (get 4 values) motif
  have result := prepend (get 1 values) currentPhase
  simpa [Code.stripPackedTransitionArgumentsCode,
    stripPackedTransitionArgumentsCost,
    prependCost, values] using result

def stripPackedTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let current := PackedWindowState.ofIndex periodicStrip first
  let next := PackedWindowState.ofIndex periodicStrip last
  packedTransitionCost tromino periodicStrip current next +
    stripPackedTransitionArgumentsCost periodicStrip first last

theorem stripPackedTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripPackedTransitionCode tromino)
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      [((PackedWindowState.ofIndex periodicStrip first).transitionBool
        tromino periodicStrip
          (PackedWindowState.ofIndex periodicStrip last)).toNat]
      (stripPackedTransitionCost
        tromino periodicStrip first last) := by
  let current := PackedWindowState.ofIndex periodicStrip first
  let next := PackedWindowState.ofIndex periodicStrip last
  simpa [Code.stripPackedTransitionCode,
    stripPackedTransitionCost, Code.packedTransitionInput,
    current, next, PackedWindowState.ofIndex] using
    comp (packedTransition
      tromino periodicStrip wellFormed current next)
      (stripPackedTransitionArguments periodicStrip first last)

def stripTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  stripPackedTransitionCost tromino periodicStrip first last +
    stripFrontierContextCost periodicStrip first last

/-- Exact fitted certificate for the explicit indexed strip edge. -/
theorem stripTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripTransitionCode tromino)
      [Encodable.encode periodicStrip, first, last]
      [(RawWindowState.indexedTransitionRawBool
        tromino periodicStrip first last).toNat]
      (stripTransitionCost
        tromino periodicStrip first last) := by
  rw [PackedWindowState.indexedTransitionRawBool_eq_packed]
  simpa [Code.stripTransitionCode,
    stripTransitionCost] using
    comp (stripPackedTransition
      tromino periodicStrip wellFormed first last)
      (stripFrontierContext periodicStrip first last)

def stripTransitionEqualityArgumentsCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  let values := [Encodable.encode periodicStrip, first, last]
  prependCost values [first] [last]
    (getCost 1 values) (getCost 2 values)

theorem stripTransitionEqualityArguments
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripTransitionEqualityArgumentsCode
      [Encodable.encode periodicStrip, first, last]
      [first, last]
      (stripTransitionEqualityArgumentsCost
        periodicStrip first last) := by
  simpa [Code.stripTransitionEqualityArgumentsCode,
    stripTransitionEqualityArgumentsCost, prependCost] using
    prepend
      (get 1 [Encodable.encode periodicStrip, first, last])
      (get 2 [Encodable.encode periodicStrip, first, last])

def stripTransitionEqualityCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  natEqCost first last +
    stripTransitionEqualityArgumentsCost periodicStrip first last

theorem stripTransitionEquality
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripTransitionEqualityCode
      [Encodable.encode periodicStrip, first, last]
      [(decide (first = last)).toNat]
      (stripTransitionEqualityCost periodicStrip first last) := by
  have result := comp (natEq first last)
    (stripTransitionEqualityArguments periodicStrip first last)
  have tagEq :
      (decide (first = last)).toNat =
        if first = last then 1 else 0 := by
    by_cases equal : first = last <;> simp [equal]
  rw [tagEq]
  simpa [Code.stripTransitionEqualityCode,
    stripTransitionEqualityCost] using result

private theorem boolOr_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolOr leftCode rightCode) values
      [(left || right).toNat]
      (boolOrCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolOr leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def stripBaseTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values := [Encodable.encode periodicStrip, first, last]
  let equal := decide (first = last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip first last
  boolOrCost values equal.toNat edge.toNat
    (stripTransitionEqualityCost periodicStrip first last)
    (stripTransitionCost tromino periodicStrip first last)

/-- Exact fitted certificate for the explicit depth-zero Savitch predicate. -/
theorem stripBaseTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripBaseTransitionCode tromino)
      [Encodable.encode periodicStrip, first, last]
      [((decide (first = last)) ||
        RawWindowState.indexedTransitionRawBool
          tromino periodicStrip first last).toNat]
      (stripBaseTransitionCost
        tromino periodicStrip first last) := by
  let equal := decide (first = last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip first last
  have result := boolOr_fit_bool equal edge
    (by simpa [equal] using
      (stripTransitionEquality periodicStrip first last))
    (by simpa [edge] using
      (stripTransition tromino periodicStrip wellFormed first last))
  simpa [Code.stripBaseTransitionCode,
    stripBaseTransitionCost, equal, edge] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
