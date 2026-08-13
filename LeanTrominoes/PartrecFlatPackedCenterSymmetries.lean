/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedCenterCandidate

/-!
# Flat packed center containment across all symmetries

The center-containment condition at one motif base is the conjunction of the
eight fixed square-symmetry candidate implications.  This file folds the flat
candidate programs into one explicit program and proves that it computes the
semantic `List.all` used by the packed frontier definition.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem boolAnd_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftCorrect : leftCode.eval values = pure [left.toNat])
    (rightCorrect : rightCode.eval values = pure [right.toNat]) :
    (boolAnd leftCode rightCode).eval values =
      pure [(left && right).toNat] := by
  have combined := boolAnd_eval_at leftCode rightCode values
    left.toNat right.toNat leftCorrect rightCorrect
  cases left <;> cases right <;> simpa using combined

/-- Conjoin flat center-containment candidate programs indexed by a fixed
list of square symmetries. -/
def flatPackedCenterSymmetryListInsideCode
    (tromino : Tromino) : List SquareSymmetry -> Code
  | [] => one
  | symmetry :: symmetries =>
      boolAnd
        (flatPackedCenterCandidateInsideCode tromino symmetry)
        (flatPackedCenterSymmetryListInsideCode tromino symmetries)

theorem flatPackedCenterSymmetryListInsideCode_eval_semantic
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterSymmetryListInsideCode tromino symmetries).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(symmetries.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat] := by
  induction symmetries with
  | nil =>
      simp [flatPackedCenterSymmetryListInsideCode]
  | cons symmetry symmetries induction =>
      have headRun := flatPackedCenterCandidateInsideCode_eval_semantic
        tromino symmetry periodicStrip wellFormed packed base
      have tailRun := induction
      simpa [flatPackedCenterSymmetryListInsideCode] using
        boolAnd_eval_at_bool
          (flatPackedCenterCandidateInsideCode tromino symmetry)
          (flatPackedCenterSymmetryListInsideCode tromino symmetries)
          (flatPackedCenterCandidateInput periodicStrip packed base)
          (packed.centerSymmetryInsideBool tromino periodicStrip
            base symmetry)
          (symmetries.all fun remaining =>
            packed.centerSymmetryInsideBool tromino periodicStrip
              base remaining)
          headRun tailRun

/-- Check all eight square-symmetry center candidates at one motif base. -/
def flatPackedCenterAllSymmetriesInsideCode
    (tromino : Tromino) : Code :=
  flatPackedCenterSymmetryListInsideCode tromino
    TrominoAssignment.squareSymmetryList

/-- The flat eight-way conjunction is exactly the symmetry fold appearing in
the semantic packed center-containment predicate. -/
@[simp]
theorem flatPackedCenterAllSymmetriesInsideCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterAllSymmetriesInsideCode tromino).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(TrominoAssignment.squareSymmetryList.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat] := by
  exact flatPackedCenterSymmetryListInsideCode_eval_semantic
    tromino TrominoAssignment.squareSymmetryList
    periodicStrip wellFormed packed base

end Turing.ToPartrec.Code
