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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
