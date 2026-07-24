import LeanTrominoes.PartrecEncodedListDecode
import LeanTrominoes.PartrecPeriodicStripDecode
import LeanTrominoes.PartrecStripCellBounds

/-!
# Explicit periodic-strip well-formedness program

The motif loop keeps the native payload

`[remainingMotifCode, allValid, width, period]`.

Each nonempty step extracts one encoded cell and its encoded tail, conjoins
the cell's fundamental-domain test with the accumulator, and retains the two
strip dimensions.  Empty states are fixed points, so the original motif code
is a safe (possibly generous) countdown.
-/

namespace LeanTrominoes

def motifInStripBounds
    (width period : Nat) (motif : List Cell) : Bool :=
  motif.all fun cell => decide (cell.InStripBounds width period)

@[simp]
theorem motifInStripBounds_nil (width period : Nat) :
    motifInStripBounds width period [] = true := by
  rfl

@[simp]
theorem motifInStripBounds_cons
    (width period : Nat) (cell : Cell)
    (remaining : List Cell) :
    motifInStripBounds width period (cell :: remaining) =
      (decide (cell.InStripBounds width period) &&
        motifInStripBounds width period remaining) := by
  rfl

theorem motifInStripBounds_eq_true_iff
    (width period : Nat) (motif : List Cell) :
    motifInStripBounds width period motif = true ↔
      ∀ cell ∈ motif, cell.InStripBounds width period := by
  simp [motifInStripBounds]

end LeanTrominoes

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input =
      outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Native loop state for a valid encoded motif suffix. -/
def stripMotifState
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : List Nat :=
  [Encodable.encode motif, valid.toNat, width, period]

/-- View the encoded motif stored in loop-state field zero. -/
def stripMotifViewCode : Code :=
  encodedListViewCode.comp (get 0)

def stripMotifHeadCellCode : Code :=
  (get 1).comp stripMotifViewCode

def stripMotifTailCode : Code :=
  (get 2).comp stripMotifViewCode

@[simp]
theorem stripMotifViewCode_eval
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    stripMotifViewCode.eval
        (stripMotifState width period valid motif) =
      pure
        (match motif with
        | [] => [0, 0, 0]
        | cell :: remaining =>
            [1, Encodable.encode cell,
              Encodable.encode remaining]) := by
  cases motif with
  | nil =>
      calc
        _ = encodedListViewCode.eval [0] := by
          simp [stripMotifViewCode, stripMotifState]
        _ = pure [0, 0, 0] :=
          encodedListViewCode_eval ([] : List Cell)
  | cons cell remaining =>
      calc
        _ = encodedListViewCode.eval
            [Encodable.encode (cell :: remaining)] := by
          simp [stripMotifViewCode, stripMotifState]
        _ = pure
            [1, Encodable.encode cell,
              Encodable.encode remaining] :=
          encodedListViewCode_eval (cell :: remaining)

@[simp]
theorem stripMotifHeadCellCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifHeadCellCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure [Encodable.encode cell] := by
  simp [stripMotifHeadCellCode]

@[simp]
theorem stripMotifTailCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifTailCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure [Encodable.encode remaining] := by
  simp [stripMotifTailCode]

/-- Assemble `[width, period, headCellCode]` for the cell predicate. -/
def stripMotifCellArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (get 3) stripMotifHeadCellCode

@[simp]
theorem stripMotifCellArgumentsCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifCellArgumentsCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure [width, period, Encodable.encode cell] := by
  have widthEval :
      (get 2).eval
          (stripMotifState width period valid
            (cell :: remaining)) =
        pure [width] := by
    simp [stripMotifState]
  have periodEval :
      (get 3).eval
          (stripMotifState width period valid
            (cell :: remaining)) =
        pure [period] := by
    simp [stripMotifState]
  simp [stripMotifCellArgumentsCode,
    widthEval, periodEval]

def stripMotifHeadInBoundsCode : Code :=
  stripCellInBoundsCode.comp
    stripMotifCellArgumentsCode

@[simp]
theorem stripMotifHeadInBoundsCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifHeadInBoundsCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure
        [if cell.InStripBounds width period then 1 else 0] := by
  simp [stripMotifHeadInBoundsCode]

def stripMotifUpdatedValidCode : Code :=
  boolAnd (get 1) stripMotifHeadInBoundsCode

@[simp]
theorem stripMotifUpdatedValidCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifUpdatedValidCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure
        [(valid &&
          decide (cell.InStripBounds width period)).toNat] := by
  have combined :=
    boolAnd_eval_at (get 1)
      stripMotifHeadInBoundsCode
      (stripMotifState width period valid
        (cell :: remaining))
      valid.toNat
      (if cell.InStripBounds width period then 1 else 0)
      (by simp [stripMotifState])
      (stripMotifHeadInBoundsCode_eval
        width period valid cell remaining)
  cases valid <;>
    by_cases inBounds :
      cell.InStripBounds width period <;>
    simp [inBounds] at combined ⊢
  all_goals exact combined

/-- Positive-state transformation for one motif cell. -/
def stripMotifConsStepCode : Code :=
  prepend stripMotifTailCode <|
    prepend stripMotifUpdatedValidCode <|
      prepend (get 2) (get 3)

@[simp]
theorem stripMotifConsStepCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifConsStepCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure
        (stripMotifState width period
          (valid &&
            decide (cell.InStripBounds width period))
          remaining) := by
  have widthEval :
      (get 2).eval
          (stripMotifState width period valid
            (cell :: remaining)) =
        pure [width] := by
    simp [stripMotifState]
  have periodEval :
      (get 3).eval
          (stripMotifState width period valid
            (cell :: remaining)) =
        pure [period] := by
    simp [stripMotifState]
  have tailEval :=
    stripMotifTailCode_eval
      width period valid cell remaining
  have updatedEval :=
    stripMotifUpdatedValidCode_eval
      width period valid cell remaining
  change
    stripMotifConsStepCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure
        [Encodable.encode remaining,
          (valid &&
            decide
              (cell.InStripBounds width period)).toNat,
          width, period]
  simp [stripMotifConsStepCode, tailEval,
    updatedEval, widthEval, periodEval]

/-- One total motif loop step; the empty motif is a fixed point. -/
def stripMotifStepCode : Code :=
  branchZero (get 0) id stripMotifConsStepCode

@[simp]
theorem stripMotifStepCode_eval_nil
    (width period : Nat) (valid : Bool) :
    stripMotifStepCode.eval
        (stripMotifState width period valid []) =
      pure (stripMotifState width period valid []) := by
  exact
    branchZero_eval_zero_at (get 0) id
      stripMotifConsStepCode
      (stripMotifState width period valid [])
      0 (by simp [stripMotifState])
      (stripMotifState width period valid [])
      (by simp) rfl

@[simp]
theorem stripMotifStepCode_eval_cons
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    stripMotifStepCode.eval
        (stripMotifState width period valid
          (cell :: remaining)) =
      pure
        (stripMotifState width period
          (valid &&
            decide (cell.InStripBounds width period))
          remaining) := by
  exact
    branchZero_eval_succ_at (get 0) id
      stripMotifConsStepCode
      (stripMotifState width period valid
        (cell :: remaining))
      (Encodable.encode (cell :: remaining))
      (by simp [stripMotifState])
      (stripMotifState width period
        (valid &&
          decide (cell.InStripBounds width period))
        remaining)
      (stripMotifConsStepCode_eval
        width period valid cell remaining)
      (by simp)

/-- Typed semantics of exactly `steps` motif iterations. -/
def stripMotifProcess
    (width period : Nat) :
    Nat → Bool → List Cell → List Nat
  | 0, valid, motif =>
      stripMotifState width period valid motif
  | steps + 1, valid, [] =>
      stripMotifProcess width period steps valid []
  | steps + 1, valid, cell :: remaining =>
      stripMotifProcess width period steps
        (valid &&
          decide (cell.InStripBounds width period))
        remaining

theorem stripMotifFlatIterateCode_eval
    (width period steps : Nat) (valid : Bool)
    (motif : List Cell) :
    (flatIterate stripMotifStepCode).eval
        (steps :: stripMotifState
          width period valid motif) =
      pure
        (stripMotifProcess width period
          steps valid motif) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing valid motif with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval,
        stripMotifProcess]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      cases motif with
      | nil =>
          refine
            ⟨steps ::
                stripMotifState width period valid [],
              ?_, ?_⟩
          · simp [flatCountdownBody,
              stripMotifStepCode_eval_nil]
          · simpa [stripMotifProcess] using
              induction valid []
      | cons cell remaining =>
          let nextValid :=
            valid &&
              decide
                (cell.InStripBounds width period)
          refine
            ⟨steps ::
                stripMotifState width period nextValid
                  remaining,
              ?_, ?_⟩
          · simp [flatCountdownBody,
              stripMotifStepCode_eval_cons,
              nextValid]
          · simpa [stripMotifProcess, nextValid] using
              induction nextValid remaining

theorem stripMotifProcess_of_length_le
    (width period steps : Nat) (valid : Bool)
    (motif : List Cell) (enough : motif.length ≤ steps) :
    stripMotifProcess width period steps valid motif =
      stripMotifState width period
        (valid && motifInStripBounds width period motif) [] := by
  induction motif generalizing steps valid with
  | nil =>
      induction steps generalizing valid with
      | zero =>
          simp [stripMotifProcess, stripMotifState]
      | succ steps induction =>
          simpa [stripMotifProcess] using induction valid
  | cons cell remaining induction =>
      cases steps with
      | zero =>
          simp at enough
      | succ steps =>
          have remainingEnough :
              remaining.length ≤ steps := by
            simpa using enough
          rw [stripMotifProcess]
          rw [induction steps
            (valid &&
              decide
                (cell.InStripBounds width period))
            remainingEnough]
          simp [stripMotifState, Bool.and_assoc]

theorem stripMotifProcess_encode
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    stripMotifProcess width period
        (Encodable.encode motif) valid motif =
      stripMotifState width period
        (valid && motifInStripBounds width period motif) [] := by
  exact stripMotifProcess_of_length_le
    width period (Encodable.encode motif) valid motif
    (length_le_encode motif)

/-- Positivity tag for the two dimensions in a decoded strip header. -/
def stripDimensionsValidCode : Code :=
  boolAnd (natPositiveCode.comp (get 0))
    (natPositiveCode.comp (get 1))

@[simp]
theorem stripDimensionsValidCode_eval
    (width period motifCode : Nat) :
    stripDimensionsValidCode.eval
        [width, period, motifCode] =
      pure
        [(decide (0 < width) &&
          decide (0 < period)).toNat] := by
  have widthRun :
      (natPositiveCode.comp (get 0)).eval
          [width, period, motifCode] =
        pure [if 0 < width then 1 else 0] := by
    simp
  have periodRun :
      (natPositiveCode.comp (get 1)).eval
          [width, period, motifCode] =
        pure [if 0 < period then 1 else 0] := by
    simp
  have combined :=
    boolAnd_eval_at
      (natPositiveCode.comp (get 0))
      (natPositiveCode.comp (get 1))
      [width, period, motifCode]
      (if 0 < width then 1 else 0)
      (if 0 < period then 1 else 0)
      widthRun periodRun
  by_cases widthPositive : 0 < width <;>
    by_cases periodPositive : 0 < period <;>
    simp [stripDimensionsValidCode,
      widthPositive, periodPositive] at combined ⊢
  all_goals exact combined

/-- Assemble the countdown and initial motif-loop payload from
`[width, period, motifCode]`. -/
def stripWellFormedLoopInputCode : Code :=
  prepend (get 2) <|
    prepend (get 2) <|
      prepend stripDimensionsValidCode <|
        prepend (get 0) (get 1)

@[simp]
theorem stripWellFormedLoopInputCode_eval
    (periodicStrip : PeriodicStrip) :
    stripWellFormedLoopInputCode.eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] =
      pure
        (Encodable.encode periodicStrip.motif ::
          stripMotifState periodicStrip.width
            periodicStrip.period
            (decide (0 < periodicStrip.width) &&
              decide (0 < periodicStrip.period))
            periodicStrip.motif) := by
  simp [stripWellFormedLoopInputCode,
    stripMotifState]

/-- Header-level program that scans the motif and projects its validity
accumulator. -/
def stripWellFormedHeaderCode : Code :=
  (get 1).comp <|
    (flatIterate stripMotifStepCode).comp
      stripWellFormedLoopInputCode

@[simp]
theorem stripWellFormedHeaderCode_eval
    (periodicStrip : PeriodicStrip) :
    stripWellFormedHeaderCode.eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] =
      pure
        [((decide (0 < periodicStrip.width) &&
            decide (0 < periodicStrip.period)) &&
          motifInStripBounds periodicStrip.width
            periodicStrip.period
            periodicStrip.motif).toNat] := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  have inputRun :=
    stripWellFormedLoopInputCode_eval periodicStrip
  have loopRun :=
    stripMotifFlatIterateCode_eval
      periodicStrip.width periodicStrip.period
      (Encodable.encode periodicStrip.motif)
      dimensionsValid periodicStrip.motif
  rw [stripMotifProcess_encode] at loopRun
  have composedLoop :
      ((flatIterate stripMotifStepCode).comp
        stripWellFormedLoopInputCode).eval
          [periodicStrip.width, periodicStrip.period,
            Encodable.encode periodicStrip.motif] =
        pure
          (stripMotifState periodicStrip.width
            periodicStrip.period
            (dimensionsValid &&
              motifInStripBounds periodicStrip.width
                periodicStrip.period
                periodicStrip.motif) []) := by
    calc
      _ = (flatIterate stripMotifStepCode).eval
          (Encodable.encode periodicStrip.motif ::
            stripMotifState periodicStrip.width
              periodicStrip.period dimensionsValid
              periodicStrip.motif) := by
        simp [inputRun, dimensionsValid]
      _ = _ := loopRun
  calc
    _ = (get 1).eval
        (stripMotifState periodicStrip.width
          periodicStrip.period
          (dimensionsValid &&
            motifInStripBounds periodicStrip.width
              periodicStrip.period
              periodicStrip.motif) []) := by
      simp [stripWellFormedHeaderCode, composedLoop]
    _ = _ := by
      simp [stripMotifState, dimensionsValid]

theorem stripWellFormedAccumulator_eq
    (periodicStrip : PeriodicStrip) :
    ((decide (0 < periodicStrip.width) &&
        decide (0 < periodicStrip.period)) &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif) =
      periodicStrip.wellFormed := by
  simp [PeriodicStrip.wellFormed,
    motifInStripBounds, Cell.InStripBounds,
    PeriodicStrip.InFundamentalDomain,
    Bool.and_assoc]

/-- Unary explicit code for `PeriodicStrip.wellFormed`. -/
def stripWellFormedExplicitCode : Code :=
  stripWellFormedHeaderCode.comp
    periodicStripHeaderCode

@[simp]
theorem stripWellFormedExplicitCode_eval
    (periodicStrip : PeriodicStrip) :
    stripWellFormedExplicitCode.eval
        [Encodable.encode periodicStrip] =
      pure [periodicStrip.wellFormed.toNat] := by
  have header :=
    periodicStripHeaderCode_eval periodicStrip
  have wellFormedHeader :=
    stripWellFormedHeaderCode_eval periodicStrip
  calc
    _ = stripWellFormedHeaderCode.eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] := by
      exact comp_eval_pure _ _ _ _ header
    _ = pure
        [((decide (0 < periodicStrip.width) &&
            decide (0 < periodicStrip.period)) &&
          motifInStripBounds periodicStrip.width
            periodicStrip.period
            periodicStrip.motif).toNat] :=
      wellFormedHeader
    _ = _ := by
      rw [stripWellFormedAccumulator_eq]

end Turing.ToPartrec.Code
