import LeanTrominoes.PartrecPair
import LeanTrominoes.PartrecStripWellFormed
import LeanTrominoes.PeriodicStripFlatEncoding

/-!
# Explicit well-formedness on flat periodic-strip fields

The target encoding presents a strip as

`[width, period, motif length, x₀, y₀, x₁, y₁, ...]`.

This evaluator keeps the loop state

`[allValid, width, period, remaining coordinates...]`

and consumes exactly two coordinate fields per iteration.  In particular,
the motif is never assembled into the recursively paired `Primcodable` list
whose binary length can be exponential in the explicit motif length.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

/-- Flat loop state for a valid encoded motif suffix. -/
def flatStripMotifState
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : List Nat :=
  [valid.toNat, width, period] ++
    motif.flatMap PeriodicStripFlatEncoding.cellFields

/-- Assemble the two leading coordinate fields for `Nat.pair`. -/
def flatStripMotifCellPairArgumentsCode : Code :=
  prepend (get 3) (get 4)

/-- Pair the leading coordinate fields into the standard `Cell` code expected
by the already verified cell-in-bounds predicate. -/
def flatStripMotifCellCode : Code :=
  natPairCode.comp flatStripMotifCellPairArgumentsCode

/-- Assemble `[width, period, cellCode]` from a flat motif-loop state. -/
def flatStripMotifCellArgumentsCode : Code :=
  prepend (get 1) <|
    prepend (get 2) flatStripMotifCellCode

def flatStripMotifHeadInBoundsCode : Code :=
  stripCellInBoundsCode.comp flatStripMotifCellArgumentsCode

def flatStripMotifUpdatedValidCode : Code :=
  boolAnd (get 0) flatStripMotifHeadInBoundsCode

/-- Consume one cell, update the validity accumulator, and retain the flat
coordinate suffix. -/
def flatStripMotifStepCode : Code :=
  prepend flatStripMotifUpdatedValidCode <|
    prepend (get 1) <|
      prepend (get 2) (drop 5)

@[simp]
theorem flatStripMotifCellPairArgumentsCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifCellPairArgumentsCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure [Encodable.encode cell.1, Encodable.encode cell.2] := by
  simp [flatStripMotifCellPairArgumentsCode,
    flatStripMotifState, PeriodicStripFlatEncoding.cellFields]

@[simp]
theorem flatStripMotifCellCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifCellCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure [Encodable.encode cell] := by
  rcases cell with ⟨x, y⟩
  simp [flatStripMotifCellCode]

@[simp]
theorem flatStripMotifCellArgumentsCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifCellArgumentsCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure [width, period, Encodable.encode cell] := by
  have cellRun :=
    flatStripMotifCellCode_eval width period valid cell remaining
  have widthRun :
      (get 1).eval
          (flatStripMotifState width period valid (cell :: remaining)) =
        pure [width] := by
    simp [flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields]
  have periodRun :
      (get 2).eval
          (flatStripMotifState width period valid (cell :: remaining)) =
        pure [period] := by
    simp [flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields]
  simp [flatStripMotifCellArgumentsCode, cellRun, widthRun, periodRun]

@[simp]
theorem flatStripMotifHeadInBoundsCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifHeadInBoundsCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure [if cell.InStripBounds width period then 1 else 0] := by
  simp [flatStripMotifHeadInBoundsCode]

@[simp]
theorem flatStripMotifUpdatedValidCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifUpdatedValidCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure
        [(valid && decide (cell.InStripBounds width period)).toNat] := by
  have combined :=
    boolAnd_eval_at (get 0) flatStripMotifHeadInBoundsCode
      (flatStripMotifState width period valid (cell :: remaining))
      valid.toNat
      (if cell.InStripBounds width period then 1 else 0)
      (by simp [flatStripMotifState])
      (flatStripMotifHeadInBoundsCode_eval
        width period valid cell remaining)
  cases valid <;>
    by_cases inBounds : cell.InStripBounds width period <;>
    simp [inBounds] at combined ⊢
  all_goals exact combined

@[simp]
theorem flatStripMotifStepCode_eval
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifStepCode.eval
        (flatStripMotifState width period valid (cell :: remaining)) =
      pure
        (flatStripMotifState width period
          (valid && decide (cell.InStripBounds width period)) remaining) := by
  have updatedRun :=
    flatStripMotifUpdatedValidCode_eval
      width period valid cell remaining
  unfold flatStripMotifStepCode
  simp only [prepend_eval_eq, updatedRun]
  simp [flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields]

/-- Total list semantics used to state the reachable-state space invariant.
Only the five-field case is reached from a valid flat strip presentation. -/
def flatStripMotifNativeStep : List Nat → List Nat
  | valid :: width :: period :: x :: y :: rest =>
      let cell : Cell :=
        (PeriodicCNFFlatEncoding.decodeIntField x,
          PeriodicCNFFlatEncoding.decodeIntField y)
      [(decide (valid ≠ 0) &&
          decide (cell.InStripBounds width period)).toNat,
        width, period] ++ rest
  | values => values

@[simp]
theorem flatStripMotifNativeStep_state_cons
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    flatStripMotifNativeStep
        (flatStripMotifState width period valid (cell :: remaining)) =
      flatStripMotifState width period
        (valid && decide (cell.InStripBounds width period)) remaining := by
  rcases cell with ⟨x, y⟩
  cases valid <;>
    by_cases inBounds : Cell.InStripBounds width period (x, y) <;>
    simp [flatStripMotifNativeStep, flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields, inBounds]

theorem flatStripMotifNativeStep_iterate
    (width period : Nat) (valid : Bool) (motif : List Cell) :
    ((flatStripMotifNativeStep)^[motif.length])
        (flatStripMotifState width period valid motif) =
      flatStripMotifState width period
        (valid && motifInStripBounds width period motif) [] := by
  induction motif generalizing valid with
  | nil =>
      simp [flatStripMotifState]
  | cons cell remaining induction =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply,
        flatStripMotifNativeStep_state_cons]
      simpa [Bool.and_assoc] using
        induction (valid && decide (cell.InStripBounds width period))

/-- Scanning exactly the explicit motif length consumes the entire coordinate
tail and accumulates precisely the conjunction of all cell bounds. -/
theorem flatStripMotifIterateCode_eval
    (width period : Nat) (valid : Bool) (motif : List Cell) :
    (flatIterate flatStripMotifStepCode).eval
        (motif.length :: flatStripMotifState width period valid motif) =
      pure
        (flatStripMotifState width period
          (valid && motifInStripBounds width period motif) []) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction motif generalizing valid with
  | nil =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval, flatStripMotifState]
  | cons cell remaining induction =>
      apply PFun.mem_fix_iff.mpr
      right
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      refine
        ⟨remaining.length ::
            flatStripMotifState width period nextValid remaining,
          ?_, ?_⟩
      · simp [flatCountdownBody, flatStripMotifStepCode_eval,
          nextValid]
      · simpa [nextValid, Bool.and_assoc] using
          induction nextValid

/-- Convert flat strip fields into the exact countdown-loop input. -/
def flatStripWellFormedLoopInputCode : Code :=
  prepend (get 2) <|
    prepend stripDimensionsValidCode <|
      prepend (get 0) <|
        prepend (get 1) (drop 3)

theorem stripDimensionsValidCode_eval_fields
    (width period : Nat) (rest : List Nat) :
    stripDimensionsValidCode.eval (width :: period :: rest) =
      pure
        [(decide (0 < width) && decide (0 < period)).toNat] := by
  have widthRun :
      (natPositiveCode.comp (get 0)).eval (width :: period :: rest) =
        pure [if 0 < width then 1 else 0] := by
    simp
  have periodRun :
      (natPositiveCode.comp (get 1)).eval (width :: period :: rest) =
        pure [if 0 < period then 1 else 0] := by
    simp
  have combined :=
    boolAnd_eval_at
      (natPositiveCode.comp (get 0))
      (natPositiveCode.comp (get 1))
      (width :: period :: rest)
      (if 0 < width then 1 else 0)
      (if 0 < period then 1 else 0)
      widthRun periodRun
  by_cases widthPositive : 0 < width <;>
    by_cases periodPositive : 0 < period <;>
    simp [stripDimensionsValidCode,
      widthPositive, periodPositive] at combined ⊢
  all_goals exact combined

@[simp]
theorem flatStripWellFormedLoopInputCode_eval
    (periodicStrip : PeriodicStrip) :
    flatStripWellFormedLoopInputCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        (periodicStrip.motif.length ::
          flatStripMotifState periodicStrip.width periodicStrip.period
            (decide (0 < periodicStrip.width) &&
              decide (0 < periodicStrip.period))
            periodicStrip.motif) := by
  rcases periodicStrip with ⟨width, period, motif⟩
  have dimensionsRun :=
    stripDimensionsValidCode_eval_fields width period
      (motif.length ::
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
  simp [flatStripWellFormedLoopInputCode,
    PeriodicStripFlatEncoding.stripFields, flatStripMotifState,
    dimensionsRun]

/-- Explicit evaluator for `PeriodicStrip.wellFormed` on the target flat
field representation. -/
def flatStripWellFormedCode : Code :=
  (get 0).comp <|
    (flatIterate flatStripMotifStepCode).comp
      flatStripWellFormedLoopInputCode

@[simp]
theorem flatStripWellFormedCode_eval (periodicStrip : PeriodicStrip) :
    flatStripWellFormedCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [periodicStrip.wellFormed.toNat] := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  have inputRun := flatStripWellFormedLoopInputCode_eval periodicStrip
  have loopRun :=
    flatStripMotifIterateCode_eval periodicStrip.width periodicStrip.period
      dimensionsValid periodicStrip.motif
  have composedLoop :
      ((flatIterate flatStripMotifStepCode).comp
        flatStripWellFormedLoopInputCode).eval
          (PeriodicStripFlatEncoding.stripFields periodicStrip) =
        pure
          (flatStripMotifState periodicStrip.width periodicStrip.period
            (dimensionsValid &&
              motifInStripBounds periodicStrip.width periodicStrip.period
                periodicStrip.motif) []) := by
    calc
      _ = (flatIterate flatStripMotifStepCode).eval
          (periodicStrip.motif.length ::
            flatStripMotifState periodicStrip.width periodicStrip.period
              dimensionsValid periodicStrip.motif) := by
        simp [inputRun, dimensionsValid]
      _ = _ := loopRun
  calc
    _ = (get 0).eval
        (flatStripMotifState periodicStrip.width periodicStrip.period
          (dimensionsValid &&
            motifInStripBounds periodicStrip.width periodicStrip.period
              periodicStrip.motif) []) := by
      simp [flatStripWellFormedCode, composedLoop]
    _ = pure
        [(dimensionsValid &&
          motifInStripBounds periodicStrip.width periodicStrip.period
            periodicStrip.motif).toNat] := by
      simp [flatStripMotifState]
    _ = _ := by
      rw [stripWellFormedAccumulator_eq]

end Turing.ToPartrec.Code
