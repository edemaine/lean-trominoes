import LeanTrominoes.PartrecDivisionSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedCenterLoopSpace
import LeanTrominoes.PartrecPackedNormalizationAllSpace
import LeanTrominoes.PartrecPackedOverlapLoopSpace
import LeanTrominoes.PartrecPackedTransition

/-!
# Evaluator-space certificate for the packed frontier transition

The exact certificates for normalization, center validity, phase advance, and
overlap are adapted to one six-field input and composed into the complete
packed transition predicate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private theorem boolAnd_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolAnd leftCode rightCode) values
      [(left && right).toNat]
      (boolAndCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolAnd leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def packedTransitionCurrentArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let restMotifWord := prependCost values
    [Encodable.encode periodicStrip.motif]
    [current.assignmentWord]
    (getCost 2 values) (getCost 3 values)
  let restPhase := prependCost values [current.phase]
    [Encodable.encode periodicStrip.motif, current.assignmentWord]
    (getCost 1 values) restMotifWord
  prependCost values [periodicStrip.period]
    [current.phase, Encodable.encode periodicStrip.motif,
      current.assignmentWord]
    (getCost 0 values) restPhase

theorem packedTransitionCurrentArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionCurrentArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [periodicStrip.period, current.phase,
        Encodable.encode periodicStrip.motif,
        current.assignmentWord]
      (packedTransitionCurrentArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have restMotifWord := prepend (get 2 values) (get 3 values)
  have restPhase := prepend (get 1 values) restMotifWord
  have result := prepend (get 0 values) restPhase
  simpa [Code.packedTransitionCurrentArgumentsCode,
    packedTransitionCurrentArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionOverlapArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let words := prependCost values [current.assignmentWord]
    [next.assignmentWord]
    (getCost 3 values) (getCost 5 values)
  prependCost values [Encodable.encode periodicStrip.motif]
    [current.assignmentWord, next.assignmentWord]
    (getCost 2 values) words

theorem packedTransitionOverlapArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      (packedTransitionOverlapArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have words := prepend (get 3 values) (get 5 values)
  have result := prepend (get 2 values) words
  simpa [Code.packedTransitionOverlapArgumentsCode,
    packedTransitionOverlapArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseDivisionArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let successorCost := succCost [current.phase] + getCost 1 values
  prependCost values [current.phase + 1] [periodicStrip.period]
    successorCost (getCost 0 values)

theorem packedTransitionPhaseDivisionArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      Code.packedTransitionPhaseDivisionArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [current.phase + 1, periodicStrip.period]
      (packedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have successor := comp (succ_named [current.phase]) (get 1 values)
  have result := prepend successor (get 0 values)
  simpa [Code.packedTransitionPhaseDivisionArgumentsCode,
    packedTransitionPhaseDivisionArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseRemainderCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  getCost 1
      [(current.phase + 1) / periodicStrip.period,
        (current.phase + 1) % periodicStrip.period] +
    (divisionSpaceBound (current.phase + 1) periodicStrip.period +
      packedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next)

theorem packedTransitionPhaseRemainder
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionPhaseRemainderCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.phase + 1) % periodicStrip.period]
      (packedTransitionPhaseRemainderCost
        periodicStrip current next) := by
  have divided := comp
    (division (current.phase + 1) periodicStrip.period)
    (packedTransitionPhaseDivisionArguments
      periodicStrip current next)
  have projected := comp
    (get 1 [(current.phase + 1) / periodicStrip.period,
      (current.phase + 1) % periodicStrip.period]) divided
  simpa [Code.packedTransitionPhaseRemainderCode,
    packedTransitionPhaseRemainderCost] using projected

def packedTransitionPhaseEqualityArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  prependCost values [next.phase]
    [(current.phase + 1) % periodicStrip.period]
    (getCost 4 values)
    (packedTransitionPhaseRemainderCost
      periodicStrip current next)

theorem packedTransitionPhaseEqualityArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      Code.packedTransitionPhaseEqualityArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [next.phase, (current.phase + 1) % periodicStrip.period]
      (packedTransitionPhaseEqualityArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have result := prepend (get 4 values)
    (packedTransitionPhaseRemainder periodicStrip current next)
  simpa [Code.packedTransitionPhaseEqualityArgumentsCode,
    packedTransitionPhaseEqualityArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  natEqCost next.phase
      ((current.phase + 1) % periodicStrip.period) +
    packedTransitionPhaseEqualityArgumentsCost
      periodicStrip current next

theorem packedTransitionPhase
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    let advances := decide
      (next.phase =
        (current.phase + 1) % periodicStrip.period)
    EvaluatorCodeFits Code.packedTransitionPhaseCode
      (Code.packedTransitionInput periodicStrip current next)
      [advances.toNat]
      (packedTransitionPhaseCost periodicStrip current next) := by
  simp only
  have result := comp
    (natEq next.phase
      ((current.phase + 1) % periodicStrip.period))
    (packedTransitionPhaseEqualityArguments
      periodicStrip current next)
  have tagEq :
      (decide (next.phase =
        (current.phase + 1) % periodicStrip.period)).toNat =
      if next.phase =
        (current.phase + 1) % periodicStrip.period then 1 else 0 := by
    by_cases advances :
        next.phase =
          (current.phase + 1) % periodicStrip.period <;>
      simp [advances]
  rw [tagEq]
  simpa [Code.packedTransitionPhaseCode,
    packedTransitionPhaseCost] using result

def packedTransitionNormalizationCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedNormalizationAllCost periodicStrip current +
    packedTransitionCurrentArgumentsCost periodicStrip current next

theorem packedTransitionNormalization
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionNormalizationCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.isNormalizedBool periodicStrip).toNat]
      (packedTransitionNormalizationCost
        periodicStrip current next) := by
  simpa [Code.packedTransitionNormalizationCode,
    packedTransitionNormalizationCost] using
    comp (packedNormalizationAll periodicStrip current)
      (packedTransitionCurrentArguments periodicStrip current next)

def packedTransitionCenterCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedCenterValidCost tromino periodicStrip current +
    packedTransitionCurrentArgumentsCost periodicStrip current next

theorem packedTransitionCenter
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.packedTransitionCenterCode tromino)
      (Code.packedTransitionInput periodicStrip current next)
      [(current.isCenterValidBool tromino periodicStrip).toNat]
      (packedTransitionCenterCost
        tromino periodicStrip current next) := by
  simpa [Code.packedTransitionCenterCode,
    packedTransitionCenterCost] using
    comp (packedCenterValid tromino periodicStrip wellFormed current)
      (packedTransitionCurrentArguments periodicStrip current next)

def packedTransitionOverlapColumnsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedOverlapColumnsCost periodicStrip current next +
    packedTransitionOverlapArgumentsCost periodicStrip current next

theorem packedTransitionOverlapColumns
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapColumnsCode
      (Code.packedTransitionInput periodicStrip current next)
      [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat]
      (packedTransitionOverlapColumnsCost
        periodicStrip current next) := by
  simpa [Code.packedTransitionOverlapColumnsCode,
    packedTransitionOverlapColumnsCost] using
    comp (packedOverlapColumns periodicStrip current next)
      (packedTransitionOverlapArguments periodicStrip current next)

def packedTransitionOverlapCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  boolAndCost values phase.toNat columns.toNat
    (packedTransitionPhaseCost periodicStrip current next)
    (packedTransitionOverlapColumnsCost
      periodicStrip current next)

theorem packedTransitionOverlap
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.overlapsBool periodicStrip next).toNat]
      (packedTransitionOverlapCost
        periodicStrip current next) := by
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  have result := boolAnd_fit_bool phase columns
    (by simpa [phase] using
      (packedTransitionPhase periodicStrip current next))
    (by simpa [columns] using
      (packedTransitionOverlapColumns periodicStrip current next))
  change EvaluatorCodeFits Code.packedTransitionOverlapCode
    (Code.packedTransitionInput periodicStrip current next)
    [(phase && columns).toNat] _
  simpa [Code.packedTransitionOverlapCode,
    packedTransitionOverlapCost, phase, columns] using result

def packedTransitionTailCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  boolAndCost values center.toNat overlap.toNat
    (packedTransitionCenterCost tromino periodicStrip current next)
    (packedTransitionOverlapCost periodicStrip current next)

theorem packedTransitionTail
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd (Code.packedTransitionCenterCode tromino)
        Code.packedTransitionOverlapCode)
      (Code.packedTransitionInput periodicStrip current next)
      [((current.isCenterValidBool tromino periodicStrip) &&
        current.overlapsBool periodicStrip next).toNat]
      (packedTransitionTailCost
        tromino periodicStrip current next) := by
  exact boolAnd_fit_bool
    (current.isCenterValidBool tromino periodicStrip)
    (current.overlapsBool periodicStrip next)
    (packedTransitionCenter
      tromino periodicStrip wellFormed current next)
    (packedTransitionOverlap periodicStrip current next)

def packedTransitionCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let normalized := current.isNormalizedBool periodicStrip
  let tail := current.isCenterValidBool tromino periodicStrip &&
    current.overlapsBool periodicStrip next
  boolAndCost values normalized.toNat tail.toNat
    (packedTransitionNormalizationCost periodicStrip current next)
    (packedTransitionTailCost tromino periodicStrip current next)

/-- Exact fitted certificate for the complete packed transition evaluator. -/
theorem packedTransition
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.packedTransitionCode tromino)
      (Code.packedTransitionInput periodicStrip current next)
      [(current.transitionBool tromino periodicStrip next).toNat]
      (packedTransitionCost tromino periodicStrip current next) := by
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  have result := boolAnd_fit_bool normalized (center && overlap)
    (by simpa [normalized] using
      (packedTransitionNormalization periodicStrip current next))
    (by simpa [center, overlap] using
      (packedTransitionTail
        tromino periodicStrip wellFormed current next))
  change EvaluatorCodeFits (Code.packedTransitionCode tromino)
    (Code.packedTransitionInput periodicStrip current next)
    [(normalized && center && overlap).toNat] _
  simpa [Code.packedTransitionCode, packedTransitionCost,
    normalized, center, overlap, Bool.and_assoc] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
