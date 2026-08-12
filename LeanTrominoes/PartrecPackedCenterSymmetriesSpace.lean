import LeanTrominoes.PartrecPackedCenterCandidateSpace
import LeanTrominoes.PartrecPackedCenterSymmetries

/-!
# Evaluator-space certificate for all packed center symmetries

This file fits the fixed eight-way center-containment conjunction by composing
the fitted candidate leaves.  The more general list-indexed helper makes the
cost recurrence transparent; the exported program specializes it to the
constant list of all square symmetries.
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

/-- Exact evaluator cost of the fixed-list symmetry conjunction. -/
def packedCenterSymmetryListInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List SquareSymmetry -> Nat
  | [] => oneCost
      (Code.packedCenterCandidateInput periodicStrip packed base)
  | symmetry :: symmetries =>
      let values :=
        Code.packedCenterCandidateInput periodicStrip packed base
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      boolAndCost values head.toNat tail.toNat
        (packedCenterCandidateInsideCost tromino symmetry
          periodicStrip packed base)
        (packedCenterSymmetryListInsideCost tromino
          periodicStrip packed base symmetries)

theorem packedCenterSymmetryListInside
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterSymmetryListInsideCode tromino symmetries)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(symmetries.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (packedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries) := by
  induction symmetries with
  | nil =>
      simpa [Code.packedCenterSymmetryListInsideCode,
        packedCenterSymmetryListInsideCost] using
        one (Code.packedCenterCandidateInput
          periodicStrip packed base)
  | cons symmetry symmetries induction =>
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      have headFit :
          EvaluatorCodeFits
            (Code.packedCenterCandidateInsideCode tromino symmetry)
            (Code.packedCenterCandidateInput periodicStrip packed base)
            [head.toNat]
            (packedCenterCandidateInsideCost tromino symmetry
              periodicStrip packed base) := by
        simpa [head] using packedCenterCandidateInside
          tromino symmetry periodicStrip wellFormed packed base
      have tailFit :
          EvaluatorCodeFits
            (Code.packedCenterSymmetryListInsideCode
              tromino symmetries)
            (Code.packedCenterCandidateInput periodicStrip packed base)
            [tail.toNat]
            (packedCenterSymmetryListInsideCost tromino
              periodicStrip packed base symmetries) := by
        simpa [tail] using induction
      simpa [Code.packedCenterSymmetryListInsideCode,
        packedCenterSymmetryListInsideCost, head, tail] using
        boolAnd_fit_bool head tail headFit tailFit

def packedCenterAllSymmetriesInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterSymmetryListInsideCost tromino periodicStrip
    packed base TrominoAssignment.squareSymmetryList

/-- Exact fitted execution of the eight-way center-containment conjunction. -/
theorem packedCenterAllSymmetriesInside
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterAllSymmetriesInsideCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(TrominoAssignment.squareSymmetryList.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (packedCenterAllSymmetriesInsideCost tromino
        periodicStrip packed base) := by
  exact packedCenterSymmetryListInside tromino
    TrominoAssignment.squareSymmetryList periodicStrip
    wellFormed packed base

end EvaluatorCodeFits

end PartrecToTM2
end Turing
