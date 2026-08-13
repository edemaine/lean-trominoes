import LeanTrominoes.PartrecFlatPackedCenterCoverage
import LeanTrominoes.PartrecFlatPackedCenterSymmetries
import LeanTrominoes.PartrecPackedCenterBase

/-!
# Flat packed center validity at one motif base

This file adds the horizontal phase guard to the flat containment and
exact-one-coverage leaves.  The resulting programs compute
`centerBaseInsideBool`, `centerBaseCoveredBool`, and their conjunction at one
motif occurrence while retaining the complete flat coordinate stream.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

private theorem boolOr_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftCorrect : leftCode.eval values = pure [left.toNat])
    (rightCorrect : rightCode.eval values = pure [right.toNat]) :
    (boolOr leftCode rightCode).eval values =
      pure [(left || right).toNat] := by
  have combined := boolOr_eval_at leftCode rightCode values
    left.toNat right.toNat leftCorrect rightCorrect
  cases left <;> cases right <;> simpa using combined

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

/-- Pair the two native base coordinates only for the existing verified
coordinate-phase predicate. -/
def flatPackedCenterBaseCellCode : Code :=
  natPairCode.comp (prepend (get 3) (get 4))

@[simp]
theorem flatPackedCenterBaseCellCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseCellCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [Encodable.encode base] := by
  rcases base with ⟨x, y⟩
  simp [flatPackedCenterBaseCellCode,
    flatPackedCenterCandidateInput]

/-- Assemble a six-field normalization-coordinate input.  A synthetic period
`phase + 1` makes the wrapped-coordinate program test direct equality between
the motif base's horizontal coordinate and `phase`. -/
def flatPackedCenterBaseCoordinateArgumentsCode : Code :=
  prepend ((succ.comp (get 1))) <|
    prepend (get 1) <|
      prepend zero <|
        prepend (numeral WindowState.center.val) <|
          prepend flatPackedCenterBaseCellCode (get 5)

@[simp]
theorem flatPackedCenterBaseCoordinateArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseCoordinateArgumentsCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [packed.phase + 1, packed.phase, 0,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord] := by
  let values := flatPackedCenterCandidateInput periodicStrip packed base
  have cellRun := flatPackedCenterBaseCellCode_eval
    periodicStrip packed base
  simp only [flatPackedCenterBaseCoordinateArgumentsCode, prepend_eval_eq]
  rw [show (succ.comp (get 1)).eval values =
      pure [packed.phase + 1] by
    simp [values, flatPackedCenterCandidateInput]]
  rw [show (get 1).eval values = pure [packed.phase] by
    simp [values, flatPackedCenterCandidateInput]]
  rw [show zero.eval values = pure [0] by simp]
  rw [show (numeral WindowState.center.val).eval values =
      pure [WindowState.center.val] by simp]
  rw [show flatPackedCenterBaseCellCode.eval values =
      pure [Encodable.encode base] by simp [values, cellRun]]
  rw [show (get 5).eval values = pure [packed.assignmentWord] by
    simp [values, flatPackedCenterCandidateInput]]
  simp

/-- Test whether the motif base lies in the packed state's center phase. -/
def flatPackedCenterBasePhaseEqualCode : Code :=
  packedNormalizedAtCoordinateCode.comp
    flatPackedCenterBaseCoordinateArgumentsCode

@[simp]
theorem flatPackedCenterBasePhaseEqualCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseEqualCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(decide (base.1 = (packed.phase : Int))).toNat] := by
  have arguments := flatPackedCenterBaseCoordinateArgumentsCode_eval
    periodicStrip packed base
  have coordinate := packedNormalizedAtCoordinateCode_eval
    (packed.phase + 1) packed.phase 0 WindowState.center.val
    packed.assignmentWord base
  rw [packedCenterSyntheticPhase_eq] at coordinate
  simpa [flatPackedCenterBasePhaseEqualCode] using
    (comp_eval_pure _ _ _ _ arguments).trans coordinate

/-- Test the phase guard used by both center-base conditions. -/
def flatPackedCenterBasePhaseDifferentCode : Code :=
  isZero flatPackedCenterBasePhaseEqualCode

@[simp]
theorem flatPackedCenterBasePhaseDifferentCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseDifferentCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(decide (base.1 ≠ (packed.phase : Int))).toNat] := by
  let equal := decide (base.1 = (packed.phase : Int))
  have equalRun :
      flatPackedCenterBasePhaseEqualCode.eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [equal.toNat] := by
    exact flatPackedCenterBasePhaseEqualCode_eval periodicStrip packed base
  have differentRaw := isZero_eval_at flatPackedCenterBasePhaseEqualCode
    (flatPackedCenterCandidateInput periodicStrip packed base)
    equal.toNat equalRun
  by_cases equality : base.1 = (packed.phase : Int)
  · simpa [flatPackedCenterBasePhaseDifferentCode, equal, equality] using
      differentRaw
  · simpa [flatPackedCenterBasePhaseDifferentCode, equal, equality] using
      differentRaw

/-- Center-containment validity at one flat motif base, including the phase
guard. -/
def flatPackedCenterBaseInsideCode (tromino : Tromino) : Code :=
  boolOr flatPackedCenterBasePhaseDifferentCode
    (flatPackedCenterAllSymmetriesInsideCode tromino)

@[simp]
theorem flatPackedCenterBaseInsideCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterBaseInsideCode tromino).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerBaseInsideBool
        tromino periodicStrip base).toNat] := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  have differentRun :
      flatPackedCenterBasePhaseDifferentCode.eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [different.toNat] := by
    exact flatPackedCenterBasePhaseDifferentCode_eval
      periodicStrip packed base
  have insideRun :
      (flatPackedCenterAllSymmetriesInsideCode tromino).eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [inside.toNat] := by
    simpa [inside] using
      flatPackedCenterAllSymmetriesInsideCode_eval_semantic
        tromino periodicStrip wellFormed packed base
  simpa [flatPackedCenterBaseInsideCode,
    PackedWindowState.centerBaseInsideBool, different, inside] using
    boolOr_eval_at_bool flatPackedCenterBasePhaseDifferentCode
      (flatPackedCenterAllSymmetriesInsideCode tromino)
      (flatPackedCenterCandidateInput periodicStrip packed base)
      different inside differentRun insideRun

/-- Exact-one center coverage at one flat motif base, including the phase
guard. -/
def flatPackedCenterBaseCoveredCode (tromino : Tromino) : Code :=
  boolOr flatPackedCenterBasePhaseDifferentCode
    (flatPackedCenterExactlyOneCoveringCode tromino)

@[simp]
theorem flatPackedCenterBaseCoveredCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterBaseCoveredCode tromino).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerBaseCoveredBool
        tromino periodicStrip base).toNat] := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  have differentRun :
      flatPackedCenterBasePhaseDifferentCode.eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [different.toNat] := by
    exact flatPackedCenterBasePhaseDifferentCode_eval
      periodicStrip packed base
  have coveredRun :
      (flatPackedCenterExactlyOneCoveringCode tromino).eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [covered.toNat] := by
    exact flatPackedCenterExactlyOneCoveringCode_eval_semantic
      tromino periodicStrip packed base
  simpa [flatPackedCenterBaseCoveredCode,
    PackedWindowState.centerBaseCoveredBool, different, covered] using
    boolOr_eval_at_bool flatPackedCenterBasePhaseDifferentCode
      (flatPackedCenterExactlyOneCoveringCode tromino)
      (flatPackedCenterCandidateInput periodicStrip packed base)
      different covered differentRun coveredRun

/-- Both center conditions at one flat motif base. -/
def flatPackedCenterBaseValidCode (tromino : Tromino) : Code :=
  boolAnd (flatPackedCenterBaseInsideCode tromino)
    (flatPackedCenterBaseCoveredCode tromino)

@[simp]
theorem flatPackedCenterBaseValidCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterBaseValidCode tromino).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [((packed.centerBaseInsideBool
          tromino periodicStrip base) &&
        packed.centerBaseCoveredBool
          tromino periodicStrip base).toNat] := by
  exact boolAnd_eval_at_bool
    (flatPackedCenterBaseInsideCode tromino)
    (flatPackedCenterBaseCoveredCode tromino)
    (flatPackedCenterCandidateInput periodicStrip packed base)
    (packed.centerBaseInsideBool tromino periodicStrip base)
    (packed.centerBaseCoveredBool tromino periodicStrip base)
    (flatPackedCenterBaseInsideCode_eval_semantic
      tromino periodicStrip wellFormed packed base)
    (flatPackedCenterBaseCoveredCode_eval_semantic
      tromino periodicStrip packed base)

end Turing.ToPartrec.Code
