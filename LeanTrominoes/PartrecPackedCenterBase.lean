import LeanTrominoes.PartrecPackedCenterCoverage
import LeanTrominoes.PartrecPackedCenterSymmetries
import LeanTrominoes.PartrecPackedNormalizedAt

/-!
# Packed center validity at one motif base

This file adds the horizontal phase guard to the previously explicit
containment and exact-one-coverage leaves.  The resulting programs compute
`centerBaseInsideBool`, `centerBaseCoveredBool`, and their conjunction at one
motif occurrence.
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

/-- At synthetic period `phase + 1`, the center column's wrapped phase is
exactly `phase`. -/
theorem packedCenterSyntheticPhase_eq (phase : Nat) :
    packedColumnPhaseNumerator
        (phase + 1) phase WindowState.center.val % (phase + 1) =
      phase := by
  have numeratorEq :
      packedColumnPhaseNumerator
          (phase + 1) phase WindowState.center.val =
        2 * (phase + 1) + phase := by
    simp [packedColumnPhaseNumerator, packedColumnPhaseSum,
      WindowState.center]
    omega
  rw [numeratorEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (Nat.lt_succ_self phase)]

/-- Assemble a six-field normalization-coordinate input.  A synthetic period
`phase + 1` makes the existing wrapped-coordinate program test direct equality
between the motif base's horizontal coordinate and `phase`. -/
def packedCenterBaseCoordinateArgumentsCode : Code :=
  prepend ((succ.comp (get 1))) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (numeral WindowState.center.val) <|
          prepend (get 3) (get 5)

@[simp]
theorem packedCenterBaseCoordinateArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBaseCoordinateArgumentsCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [packed.phase + 1, packed.phase,
        Encodable.encode periodicStrip.motif,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord] := by
  simp [packedCenterBaseCoordinateArgumentsCode,
    packedCenterCandidateInput]

/-- Test whether the motif base lies in the packed state's center phase. -/
def packedCenterBasePhaseEqualCode : Code :=
  packedNormalizedAtCoordinateCode.comp
    packedCenterBaseCoordinateArgumentsCode

@[simp]
theorem packedCenterBasePhaseEqualCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBasePhaseEqualCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide (base.1 = (packed.phase : Int))).toNat] := by
  have arguments := packedCenterBaseCoordinateArgumentsCode_eval
    periodicStrip packed base
  have coordinate := packedNormalizedAtCoordinateCode_eval
    (packed.phase + 1) packed.phase
    (Encodable.encode periodicStrip.motif)
    WindowState.center.val packed.assignmentWord base
  rw [packedCenterSyntheticPhase_eq] at coordinate
  simpa [packedCenterBasePhaseEqualCode] using
    (comp_eval_pure _ _ _ _ arguments).trans coordinate

/-- Test the phase guard used by both center-base conditions. -/
def packedCenterBasePhaseDifferentCode : Code :=
  isZero packedCenterBasePhaseEqualCode

@[simp]
theorem packedCenterBasePhaseDifferentCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBasePhaseDifferentCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide (base.1 ≠ (packed.phase : Int))).toNat] := by
  let equal := decide (base.1 = (packed.phase : Int))
  have equalRun :
      packedCenterBasePhaseEqualCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
        pure [equal.toNat] := by
    exact packedCenterBasePhaseEqualCode_eval periodicStrip packed base
  have differentRaw := isZero_eval_at packedCenterBasePhaseEqualCode
    (packedCenterCandidateInput periodicStrip packed base)
    equal.toNat equalRun
  by_cases equality : base.1 = (packed.phase : Int)
  · simpa [packedCenterBasePhaseDifferentCode, equal, equality] using
      differentRaw
  · simpa [packedCenterBasePhaseDifferentCode, equal, equality] using
      differentRaw

/-- Center-containment validity at one motif base, including the phase guard. -/
def packedCenterBaseInsideCode (tromino : Tromino) : Code :=
  boolOr packedCenterBasePhaseDifferentCode
    (packedCenterAllSymmetriesInsideCode tromino)

@[simp]
theorem packedCenterBaseInsideCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterBaseInsideCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerBaseInsideBool
        tromino periodicStrip base).toNat] := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  have differentRun :
      packedCenterBasePhaseDifferentCode.eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [different.toNat] := by
    exact packedCenterBasePhaseDifferentCode_eval periodicStrip packed base
  have insideRun :
      (packedCenterAllSymmetriesInsideCode tromino).eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [inside.toNat] := by
    simpa [inside] using packedCenterAllSymmetriesInsideCode_eval_semantic
      tromino periodicStrip wellFormed packed base
  simpa [packedCenterBaseInsideCode,
    PackedWindowState.centerBaseInsideBool, different, inside] using
    boolOr_eval_at_bool packedCenterBasePhaseDifferentCode
      (packedCenterAllSymmetriesInsideCode tromino)
      (packedCenterCandidateInput periodicStrip packed base)
      different inside differentRun insideRun

/-- Exact-one center coverage at one motif base, including the phase guard. -/
def packedCenterBaseCoveredCode (tromino : Tromino) : Code :=
  boolOr packedCenterBasePhaseDifferentCode
    (packedCenterExactlyOneCoveringCode tromino)

@[simp]
theorem packedCenterBaseCoveredCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterBaseCoveredCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerBaseCoveredBool
        tromino periodicStrip base).toNat] := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  have differentRun :
      packedCenterBasePhaseDifferentCode.eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [different.toNat] := by
    exact packedCenterBasePhaseDifferentCode_eval periodicStrip packed base
  have coveredRun :
      (packedCenterExactlyOneCoveringCode tromino).eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [covered.toNat] := by
    exact packedCenterExactlyOneCoveringCode_eval_semantic
      tromino periodicStrip packed base
  simpa [packedCenterBaseCoveredCode,
    PackedWindowState.centerBaseCoveredBool, different, covered] using
    boolOr_eval_at_bool packedCenterBasePhaseDifferentCode
      (packedCenterExactlyOneCoveringCode tromino)
      (packedCenterCandidateInput periodicStrip packed base)
      different covered differentRun coveredRun

/-- Both center conditions at one motif base. -/
def packedCenterBaseValidCode (tromino : Tromino) : Code :=
  boolAnd (packedCenterBaseInsideCode tromino)
    (packedCenterBaseCoveredCode tromino)

@[simp]
theorem packedCenterBaseValidCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterBaseValidCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [((packed.centerBaseInsideBool
          tromino periodicStrip base) &&
        packed.centerBaseCoveredBool
          tromino periodicStrip base).toNat] := by
  exact boolAnd_eval_at_bool
    (packedCenterBaseInsideCode tromino)
    (packedCenterBaseCoveredCode tromino)
    (packedCenterCandidateInput periodicStrip packed base)
    (packed.centerBaseInsideBool tromino periodicStrip base)
    (packed.centerBaseCoveredBool tromino periodicStrip base)
    (packedCenterBaseInsideCode_eval_semantic
      tromino periodicStrip wellFormed packed base)
    (packedCenterBaseCoveredCode_eval_semantic
      tromino periodicStrip packed base)

end Turing.ToPartrec.Code
