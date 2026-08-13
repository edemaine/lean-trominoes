/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedAssignmentAtSpace
import LeanTrominoes.PartrecPackedTargetCellSpace
import LeanTrominoes.PartrecPackedTargetMembership

/-!
# Evaluator-space certificate for packed target membership

This file fits the canonical target-cell construction, the four-field packed
motif scan, and the final `found`-bit projection compositionally.  The exact
cost is continuation-independent, so later fixed tromino checks can reuse the
leaf without allocating a decoded motif or frontier assignment.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private def packedTargetMembershipValues
    (period phase motifCode rowCode word : Nat) : List Nat :=
  [period, phase, motifCode, rowCode, word]

def packedTargetMembershipTargetArgumentsCost
    (column : WindowColumn)
    (period phase motifCode rowCode word : Nat) : Nat :=
  let values :=
    packedTargetMembershipValues period phase motifCode rowCode word
  let restRow :=
    prependCost values [column.val] [rowCode]
      (numeralCost column.val values) (getCost 3 values)
  let restPhase :=
    prependCost values [phase] [column.val, rowCode]
      (getCost 1 values) restRow
  prependCost values [period] [phase, column.val, rowCode]
    (getCost 0 values) restPhase

theorem packedTargetMembershipTargetArguments
    (column : WindowColumn)
    (period phase motifCode rowCode word : Nat) :
    EvaluatorCodeFits
      (Code.packedTargetMembershipTargetArgumentsCode column)
      (packedTargetMembershipValues
        period phase motifCode rowCode word)
      [period, phase, column.val, rowCode]
      (packedTargetMembershipTargetArgumentsCost
        column period phase motifCode rowCode word) := by
  let values :=
    packedTargetMembershipValues period phase motifCode rowCode word
  have restRow :=
    prepend (numeral column.val values) (get 3 values)
  have restPhase := prepend (get 1 values) restRow
  have result := prepend (get 0 values) restPhase
  simpa [Code.packedTargetMembershipTargetArgumentsCode,
    packedTargetMembershipTargetArgumentsCost,
    packedTargetMembershipValues, Code.numeral,
    numeralCost, prependCost, values] using result

def packedTargetMembershipTargetCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase motifCode rowCode word : Nat) : Nat :=
  packedTargetCellCost verticalOffset
      period phase column.val rowCode +
    packedTargetMembershipTargetArgumentsCost
      column period phase motifCode rowCode word

theorem packedTargetMembershipTarget
    (column : WindowColumn) (verticalOffset : Int)
    (period phase motifCode word : Nat) (row : Int) :
    let x :=
      Code.packedColumnPhaseNumerator
        period phase column.val % period
    let target : Cell :=
      (Int.ofNat x, row + verticalOffset)
    EvaluatorCodeFits
      (Code.packedTargetMembershipTargetCode
        column verticalOffset)
      (packedTargetMembershipValues period phase motifCode
        (Encodable.encode row) word)
      [Encodable.encode target]
      (packedTargetMembershipTargetCost column verticalOffset
        period phase motifCode (Encodable.encode row) word) := by
  simp only
  simpa [Code.packedTargetMembershipTargetCode,
    packedTargetMembershipTargetCost] using
    comp
      (packedTargetCell_encode verticalOffset
        period phase column.val row)
      (packedTargetMembershipTargetArguments column
        period phase motifCode (Encodable.encode row) word)

def packedTargetMembershipLookupArgumentsCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let values :=
    packedTargetMembershipValues period phase
      (Encodable.encode motif) (Encodable.encode row) word
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let restWord :=
    prependCost values [Encodable.encode target] [word]
      (packedTargetMembershipTargetCost column verticalOffset
        period phase (Encodable.encode motif)
          (Encodable.encode row) word)
      (getCost 4 values)
  let restColumn :=
    prependCost values [column.val]
      [Encodable.encode target, word]
      (numeralCost column.val values) restWord
  prependCost values [Encodable.encode motif]
    [column.val, Encodable.encode target, word]
    (getCost 2 values) restColumn

theorem packedTargetMembershipLookupArguments
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x :=
      Code.packedColumnPhaseNumerator
        period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    EvaluatorCodeFits
      (Code.packedTargetMembershipLookupArgumentsCode
        column verticalOffset)
      (packedTargetMembershipValues period phase
        (Encodable.encode motif) (Encodable.encode row) word)
      [Encodable.encode motif, column.val,
        Encodable.encode target, word]
      (packedTargetMembershipLookupArgumentsCost
        column verticalOffset period phase motif row word) := by
  simp only
  let values :=
    packedTargetMembershipValues period phase
      (Encodable.encode motif) (Encodable.encode row) word
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  have restWord := prepend
    (packedTargetMembershipTarget column verticalOffset
      period phase (Encodable.encode motif) word row)
    (get 4 values)
  have restColumn :=
    prepend (numeral column.val values) restWord
  have result := prepend (get 2 values) restColumn
  simpa [Code.packedTargetMembershipLookupArgumentsCode,
    packedTargetMembershipLookupArgumentsCost,
    packedTargetMembershipValues, Code.numeral,
    numeralCost, prependCost, values, x, target] using result

def packedTargetMembershipLookupCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  packedAssignmentLookupCodeCost motif column.val target word +
    packedTargetMembershipLookupArgumentsCost
      column verticalOffset period phase motif row word

theorem packedTargetMembershipLookup
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x :=
      Code.packedColumnPhaseNumerator
        period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    let outcome :=
      Code.packedAssignmentLookupOutcome
        motif column.val target word
    EvaluatorCodeFits
      (Code.packedAssignmentLookupCode.comp
        (Code.packedTargetMembershipLookupArgumentsCode
          column verticalOffset))
      (packedTargetMembershipValues period phase
        (Encodable.encode motif) (Encodable.encode row) word)
      [outcome.2.1, outcome.2.2.toNat]
      (packedTargetMembershipLookupCost
        column verticalOffset period phase motif row word) := by
  simp only
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  simpa [packedTargetMembershipLookupCost, x, target] using
    comp
      (packedAssignmentLookup motif column.val target word)
      (packedTargetMembershipLookupArguments
        column verticalOffset period phase motif row word)

def packedTargetMembershipCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let outcome :=
    Code.packedAssignmentLookupOutcome motif column.val target word
  getCost 1 [outcome.2.1, outcome.2.2.toNat] +
    packedTargetMembershipLookupCost
      column verticalOffset period phase motif row word

/-- Exact fitted execution of the complete packed target-membership leaf. -/
theorem packedTargetMembership
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x :=
      Code.packedColumnPhaseNumerator
        period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    let outcome :=
      Code.packedAssignmentLookupOutcome motif column.val target word
    EvaluatorCodeFits
      (Code.packedTargetMembershipCode column verticalOffset)
      (packedTargetMembershipValues period phase
        (Encodable.encode motif) (Encodable.encode row) word)
      [outcome.2.2.toNat]
      (packedTargetMembershipCost
        column verticalOffset period phase motif row word) := by
  simp only
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let outcome :=
    Code.packedAssignmentLookupOutcome motif column.val target word
  simpa [Code.packedTargetMembershipCode,
    packedTargetMembershipCost, outcome, x, target] using
    comp (get 1 [outcome.2.1, outcome.2.2.toNat])
      (packedTargetMembershipLookup
        column verticalOffset period phase motif row word)

theorem packedTargetMembership_contains
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (row : Int) :
    EvaluatorCodeFits
      (Code.packedTargetMembershipCode column verticalOffset)
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        Encodable.encode row, packed.assignmentWord]
      [(periodicStrip.contains
        ((packed.phase : Int) + column.displacement,
          row + verticalOffset)).toNat]
      (packedTargetMembershipCost column verticalOffset
        periodicStrip.period packed.phase periodicStrip.motif
          row packed.assignmentWord) := by
  let x :=
    Code.packedColumnPhaseNumerator periodicStrip.period
      packed.phase column.val % periodicStrip.period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let canonical : Cell :=
    ((packed.columnPhase periodicStrip column : Int),
      row + verticalOffset)
  let outcome :=
    Code.packedAssignmentLookupOutcome periodicStrip.motif
      column.val target packed.assignmentWord
  have targetEq : target = canonical := by
    apply Prod.ext
    · simp only [target, canonical, x,
        PackedWindowState.columnPhase,
        Code.packedColumnPhaseNumerator,
        Code.packedColumnPhaseSum]
      congr 2
      omega
    · rfl
  have foundEq :
      outcome.2.2 =
        periodicStrip.contains
          ((packed.phase : Int) + column.displacement,
            row + verticalOffset) := by
    rw [show outcome.2.2 = decide (target ∈ periodicStrip.motif) by
      simpa [outcome] using
        Code.packedAssignmentLookupOutcome_found_eq_decide_mem
          periodicStrip.motif column target packed.assignmentWord]
    rw [targetEq]
    apply Eq.symm
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact PackedWindowState.contains_column_eq_true_iff_mem_motif
      periodicStrip wellFormed packed column (row + verticalOffset)
  have fitted := packedTargetMembership column verticalOffset
    periodicStrip.period packed.phase periodicStrip.motif
      row packed.assignmentWord
  change EvaluatorCodeFits
    (Code.packedTargetMembershipCode column verticalOffset)
    (packedTargetMembershipValues periodicStrip.period packed.phase
      (Encodable.encode periodicStrip.motif) (Encodable.encode row)
      packed.assignmentWord)
    [(periodicStrip.contains
      ((packed.phase : Int) + column.displacement,
        row + verticalOffset)).toNat]
    (packedTargetMembershipCost column verticalOffset
      periodicStrip.period packed.phase periodicStrip.motif
        row packed.assignmentWord)
  rw [← foundEq]
  simpa [x, target, outcome] using fitted

/-- One numeric envelope containing every native field exposed while checking
one translated target cell.  The canonical target code is included explicitly;
its own construction is controlled by `packedTargetCellUnit`. -/
def packedTargetMembershipLimit
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  period + phase + Encodable.encode motif + Encodable.encode row + word +
    column.val + Encodable.encode target + 100

/-- Shared workspace unit for target construction, packed assignment lookup,
and all fixed-width adapters in one membership call. -/
def packedTargetMembershipUnit
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x :=
    Code.packedColumnPhaseNumerator
      period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  packedTargetCellUnit verticalOffset period phase column.val
      (Encodable.encode row) +
    packedAssignmentLookupSpaceBound
      (Encodable.encode motif) column.val
      (Encodable.encode target) word +
    (encodedListSpace
      [packedTargetMembershipLimit column verticalOffset
        period phase motif row word] + 1)

/-- Direct bit-length unit for one translated target-membership query. -/
def packedTargetMembershipBitUnit
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  (Computability.encodeNat period).length +
    (Computability.encodeNat phase).length +
    (Computability.encodeNat (Encodable.encode motif)).length +
    (Computability.encodeNat (Encodable.encode row)).length +
    (Computability.encodeNat word).length +
    (Computability.encodeNat column.val).length +
    (Computability.encodeNat
      (intOffsetAmount verticalOffset)).length + 1

set_option maxHeartbeats 1200000 in
/-- The composed target-construction and assignment-lookup unit is linear in
the original query-field bit lengths. -/
theorem packedTargetMembershipUnit_le_linear
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    packedTargetMembershipUnit column verticalOffset
        period phase motif row word ≤
      100000000000000000000000000 * packedTargetMembershipBitUnit
        column verticalOffset period phase motif row word := by
  let amount := intOffsetAmount verticalOffset
  let motifCode := Encodable.encode motif
  let rowCode := Encodable.encode row
  let numerator := Code.packedColumnPhaseNumerator period phase column.val
  let x := numerator % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let targetCode := Encodable.encode target
  let bitUnit := packedTargetMembershipBitUnit
    column verticalOffset period phase motif row word
  have bitUnitPositive : 0 < bitUnit := by
    simp [bitUnit, packedTargetMembershipBitUnit]
  have cellUnit := packedTargetCellUnit_le_linear
    verticalOffset period phase column.val rowCode
  have numeratorBound :
      numerator ≤ phase + column.val + (period + period) := by
    simp only [numerator, Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum]
    omega
  have xBound : x ≤ phase + column.val + (period + period) :=
    (Nat.mod_le numerator period).trans numeratorBound
  have periodDouble := encodeNat_add_length_le_sum period period
  have phaseColumn := encodeNat_add_length_le_sum phase column.val
  have xLimit := encodeNat_add_length_le_sum
    (phase + column.val) (period + period)
  have xBits :
      (Computability.encodeNat x).length ≤
        (Computability.encodeNat phase).length +
          (Computability.encodeNat column.val).length +
          2 * (Computability.encodeNat period).length + 3 := by
    have raw := (encodeNat_length_mono xBound).trans xLimit
    omega
  have firstCodeBits := encodeNat_mul_length_le_sum 2 x
  have yCodeBits :
      (Computability.encodeNat yCode).length ≤
        10 * ((Computability.encodeNat rowCode).length +
          (Computability.encodeNat amount).length + 1) := by
    simpa [yCode, amount] using
      intOffsetResultCode_length_le verticalOffset rowCode
  have targetPairBits := encodeNat_pair_length_le (2 * x) yCode
  have targetCodeBits :
      (Computability.encodeNat targetCode).length ≤
        100 * bitUnit := by
    have twoBits :
        (Computability.encodeNat 2).length = 2 := by native_decide
    have targetEq : targetCode = Nat.pair (2 * x) yCode := by
      change Encodable.encode
          ((Int.ofNat x, row + verticalOffset) : Cell) =
        Nat.pair (2 * x) yCode
      rw [Encodable.encode_prod_val, IntEncoding.encode_ofNat]
      congr 1
      simp [yCode, rowCode]
    rw [targetEq]
    simp only [bitUnit, packedTargetMembershipBitUnit]
    simp only [amount, rowCode] at yCodeBits
    clear * - xBits firstCodeBits yCodeBits targetPairBits twoBits
    omega
  have lookup := packedAssignmentLookupSpaceBound_le_linear
    motifCode column.val targetCode word
  have lookupGlobal :
      packedAssignmentLookupSpaceBound
          motifCode column.val targetCode word ≤
        10000000000000000000000000 * bitUnit := by
    simp only [packedAssignmentLookupInputUnit,
      encodedListSpace_cons, encodedListSpace_nil] at lookup
    simp only [bitUnit, packedTargetMembershipBitUnit,
      motifCode] at lookup targetCodeBits ⊢
    clear * - lookup targetCodeBits
    omega
  have limit1 := encodeNat_add_length_le_sum period phase
  have limit2 := encodeNat_add_length_le_sum (period + phase) motifCode
  have limit3 := encodeNat_add_length_le_sum
    (period + phase + motifCode) rowCode
  have limit4 := encodeNat_add_length_le_sum
    (period + phase + motifCode + rowCode) word
  have limit5 := encodeNat_add_length_le_sum
    (period + phase + motifCode + rowCode + word) column.val
  have limit6 := encodeNat_add_length_le_sum
    (period + phase + motifCode + rowCode + word + column.val) targetCode
  have limit7 := encodeNat_add_length_le_sum
    (period + phase + motifCode + rowCode + word + column.val + targetCode) 100
  have limitBits :
      (Computability.encodeNat
        (period + phase + motifCode + rowCode + word +
          column.val + targetCode + 100)).length ≤
        1000 * bitUnit := by
    have hundredBits :
        (Computability.encodeNat 100).length = 7 := by native_decide
    simp only [motifCode, rowCode] at limit1 limit2 limit3
    simp only [motifCode, rowCode] at limit4 limit5 limit6 limit7
    simp only [bitUnit, packedTargetMembershipBitUnit,
      motifCode, rowCode] at targetCodeBits ⊢
    clear * - limit1 limit2 limit3 limit4 limit5 limit6 limit7
      targetCodeBits hundredBits
    omega
  have cellGlobal :
      packedTargetCellUnit verticalOffset period phase column.val rowCode ≤
        100000 * bitUnit := by
    simp only [rowCode] at cellUnit
    simp only [bitUnit, packedTargetMembershipBitUnit, rowCode]
    omega
  simp only [packedTargetMembershipUnit,
    packedTargetMembershipLimit,
    encodedListSpace_cons, encodedListSpace_nil]
  change
    packedTargetCellUnit verticalOffset period phase column.val rowCode +
        packedAssignmentLookupSpaceBound
          motifCode column.val targetCode word +
        ((Computability.encodeNat
          (period + phase + motifCode + rowCode + word +
            column.val + targetCode + 100)).length + 2) ≤ _
  simp only [bitUnit, motifCode, rowCode] at cellGlobal lookupGlobal limitBits ⊢
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
/-- The complete streamed membership leaf has a uniform input-linear
workspace estimate in the shared arithmetic/lookup unit. -/
theorem packedTargetMembershipCost_le_linear
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    packedTargetMembershipCost column verticalOffset
        period phase motif row word ≤
      1000000000000000000000000000000000000000000000000000000 *
        (intOffsetAmount verticalOffset + 1) *
        packedTargetMembershipUnit column verticalOffset
          period phase motif row word := by
  let motifCode := Encodable.encode motif
  let rowCode := Encodable.encode row
  let x :=
    Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let targetCode := Encodable.encode target
  let outcome :=
    Code.packedAssignmentLookupOutcome motif column.val target word
  let values :=
    packedTargetMembershipValues period phase motifCode rowCode word
  let limit := packedTargetMembershipLimit column verticalOffset
    period phase motif row word
  let localUnit := encodedListSpace [limit] + 1
  let unit := packedTargetMembershipUnit column verticalOffset
    period phase motif row word
  have localUnitPositive : 1 ≤ localUnit := by
    simp [localUnit]
  have unitPositive : 1 ≤ unit := by
    dsimp only [unit, packedTargetMembershipUnit]
    omega
  have localUnitLe : localUnit ≤ unit := by
    dsimp only [localUnit, unit, packedTargetMembershipUnit, limit]
    omega
  have unitLeScaled :
      unit ≤ (intOffsetAmount verticalOffset + 1) * unit := by
    calc
      unit = 1 * unit := by simp
      _ ≤ (intOffsetAmount verticalOffset + 1) * unit := by
        gcongr
        omega
  have localUnitLeScaled :
      localUnit ≤ (intOffsetAmount verticalOffset + 1) * unit :=
    localUnitLe.trans unitLeScaled
  have periodBound : period ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have phaseBound : phase ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have motifBound : motifCode ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have rowBound : rowCode ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have wordBound : word ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have columnBound : column.val ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target]
    omega
  have targetBound : targetCode ≤ limit := by
    simp [limit, packedTargetMembershipLimit, motifCode, rowCode,
      targetCode, target, x]
    omega
  have outcomeDigit : outcome.2.1 ≤ 40 := by
    simpa [outcome, target] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif column.val target word
  have outcomeDigitBound : outcome.2.1 ≤ limit := by
    simp [limit, packedTargetMembershipLimit]
    omega
  have foundBound : outcome.2.2.toNat ≤ limit := by
    cases outcome.2.2 <;>
      simp [limit, packedTargetMembershipLimit]
  have inputSpace : encodedListSpace values ≤ 6 * localUnit := by
    have raw := encodedListSpace_le_of_fields_le values limit (by
      intro value member
      simp only [values, packedTargetMembershipValues,
        List.mem_cons] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | impossible
      · exact periodBound
      · exact phaseBound
      · exact motifBound
      · exact rowBound
      · exact wordBound
      · simp at impossible)
    simp only [values, packedTargetMembershipValues,
      List.length_cons, List.length_nil] at raw
    change encodedListSpace
      [period, phase, motifCode, rowCode, word] ≤ 6 * localUnit
    simp only [localUnit, encodedListSpace_cons,
      encodedListSpace_nil] at raw ⊢
    omega
  have listTwoSpace :
      encodedListSpace [outcome.2.1, outcome.2.2.toNat] ≤
        3 * localUnit := by
    have raw := encodedListSpace_le_of_fields_le
      [outcome.2.1, outcome.2.2.toNat] limit (by
        intro value member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | impossible
        · exact outcomeDigitBound
        · exact foundBound
        · simp at impossible)
    simp only [List.length_cons, List.length_nil] at raw
    simp only [localUnit, encodedListSpace_cons,
      encodedListSpace_nil] at raw ⊢
    omega
  have getResult := listCodeGetCost_le_linear 1
    [outcome.2.1, outcome.2.2.toNat]
  have getResultBound :
      getCost 1 [outcome.2.1, outcome.2.2.toNat] ≤
        100000 * localUnit := by
    omega
  have targetCost := packedTargetCellCost_le_linear verticalOffset
    period phase column.val rowCode
  have targetCostBound :
      packedTargetCellCost verticalOffset
          period phase column.val rowCode ≤
        1000000000000000000000000000000000000000000000 *
          (intOffsetAmount verticalOffset + 1) * unit := by
    have targetUnitLe :
        packedTargetCellUnit verticalOffset period phase
            column.val rowCode ≤ unit := by
      dsimp only [unit, packedTargetMembershipUnit, rowCode]
      omega
    exact targetCost.trans (Nat.mul_le_mul_left _ targetUnitLe)
  have lookupCost := packedAssignmentLookupCodeCost_le_linear
    motif column.val target word
  have lookupCostExplicit :
      packedAssignmentLookupCodeCost motif column.val target word ≤
        packedAssignmentLookupSpaceBound
          (Encodable.encode motif) column.val
          (Encodable.encode
            ((Int.ofNat
              (Code.packedColumnPhaseNumerator period phase
                column.val % period), row + verticalOffset) : Cell))
          word := by
    simpa [target, x] using lookupCost
  have lookupCostBound :
      packedAssignmentLookupCodeCost motif column.val target word ≤
        unit := by
    dsimp only [unit, packedTargetMembershipUnit]
    exact lookupCostExplicit.trans (by omega)
  have get0 := listCodeGetCost_le_linear 0 values
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get3 := listCodeGetCost_le_linear 3 values
  have get4 := listCodeGetCost_le_linear 4 values
  have get0Bound : getCost 0 values ≤ 1000000 * localUnit := by omega
  have get1Bound : getCost 1 values ≤ 1000000 * localUnit := by omega
  have get2Bound : getCost 2 values ≤ 1000000 * localUnit := by omega
  have get3Bound : getCost 3 values ≤ 1000000 * localUnit := by omega
  have get4Bound : getCost 4 values ≤ 1000000 * localUnit := by omega
  have numeralBound :
      numeralCost column.val values ≤ 1000000000 * localUnit := by
    have zeroBound := listCodeZeroCost_le_linear values
    have addSmall : addConstCost column.val [0] ≤ 100000 := by
      fin_cases column <;> native_decide
    simp only [numeralCost]
    omega
  have inputSpaceExplicit :
      encodedListSpace [period, phase, motifCode, rowCode, word] ≤
        6 * localUnit := by
    simpa [values, packedTargetMembershipValues] using inputSpace
  have get0Explicit :
      getCost 0 [period, phase, motifCode, rowCode, word] ≤
        1000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using get0Bound
  have get1Explicit :
      getCost 1 [period, phase, motifCode, rowCode, word] ≤
        1000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using get1Bound
  have get2Explicit :
      getCost 2 [period, phase, motifCode, rowCode, word] ≤
        1000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using get2Bound
  have get3Explicit :
      getCost 3 [period, phase, motifCode, rowCode, word] ≤
        1000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using get3Bound
  have get4Explicit :
      getCost 4 [period, phase, motifCode, rowCode, word] ≤
        1000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using get4Bound
  have numeralExplicit :
      numeralCost column.val
          [period, phase, motifCode, rowCode, word] ≤
        1000000000 * localUnit := by
    simpa [values, packedTargetMembershipValues] using numeralBound
  have targetArgumentsBound :
      packedTargetMembershipTargetArgumentsCost column
          period phase motifCode rowCode word ≤
        1000000000000000000 * localUnit := by
    simp [packedTargetMembershipTargetArgumentsCost,
      prependCost, values, packedTargetMembershipValues]
    simp [values, packedTargetMembershipValues] at inputSpace
    have periodBits := listCodeEncodeNat_length_mono periodBound
    have phaseBits := listCodeEncodeNat_length_mono phaseBound
    have rowBits := listCodeEncodeNat_length_mono rowBound
    have columnBits := listCodeEncodeNat_length_mono columnBound
    simp only [localUnit, encodedListSpace_cons,
      encodedListSpace_nil] at *
    omega
  have targetTotalBound :
      packedTargetMembershipTargetCost column verticalOffset
          period phase motifCode rowCode word ≤
        10000000000000000000000000000000000000000000000 *
          (intOffsetAmount verticalOffset + 1) * unit := by
    simp only [packedTargetMembershipTargetCost]
    simp only [Nat.mul_assoc] at targetCostBound ⊢
    omega
  have targetTotalExplicit :
      packedTargetMembershipTargetCost column verticalOffset
          period phase (Encodable.encode motif) (Encodable.encode row) word ≤
        10000000000000000000000000000000000000000000000 *
          (intOffsetAmount verticalOffset + 1) * unit := by
    simpa [motifCode, rowCode] using targetTotalBound
  have targetTotalExplicitScaled :
      packedTargetMembershipTargetCost column verticalOffset
          period phase (Encodable.encode motif) (Encodable.encode row) word ≤
        10000000000000000000000000000000000000000000000 *
          ((intOffsetAmount verticalOffset + 1) * unit) := by
    simpa only [Nat.mul_assoc] using targetTotalExplicit
  have inputSpaceLookup :
      encodedListSpace
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] ≤
        6 * localUnit := by
    simpa [motifCode, rowCode] using inputSpaceExplicit
  have get2Lookup :
      getCost 2
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] ≤
        1000000 * localUnit := by
    simpa [motifCode, rowCode] using get2Explicit
  have get4Lookup :
      getCost 4
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] ≤
        1000000 * localUnit := by
    simpa [motifCode, rowCode] using get4Explicit
  have numeralLookup :
      numeralCost column.val
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] ≤
        1000000000 * localUnit := by
    simpa [motifCode, rowCode] using numeralExplicit
  have inputSpaceLookupValues :
      encodedListSpace
          (packedTargetMembershipValues period phase
            (Encodable.encode motif) (Encodable.encode row) word) ≤
        6 * localUnit := by
    simpa [packedTargetMembershipValues] using inputSpaceLookup
  have get2LookupValues :
      getCost 2
          (packedTargetMembershipValues period phase
            (Encodable.encode motif) (Encodable.encode row) word) ≤
        1000000 * localUnit := by
    simpa [packedTargetMembershipValues] using get2Lookup
  have get4LookupValues :
      getCost 4
          (packedTargetMembershipValues period phase
            (Encodable.encode motif) (Encodable.encode row) word) ≤
        1000000 * localUnit := by
    simpa [packedTargetMembershipValues] using get4Lookup
  have numeralLookupValues :
      numeralCost column.val
          (packedTargetMembershipValues period phase
            (Encodable.encode motif) (Encodable.encode row) word) ≤
        1000000000 * localUnit := by
    simpa [packedTargetMembershipValues] using numeralLookup
  have lookupArgumentsBound :
      packedTargetMembershipLookupArgumentsCost column verticalOffset
          period phase motif row word ≤
        10000000000000000000000000000000000000000000000000 *
          (intOffsetAmount verticalOffset + 1) * unit := by
    simp [packedTargetMembershipLookupArgumentsCost,
      prependCost, values, motifCode, rowCode, x, target,
      targetCode]
    have motifBits := listCodeEncodeNat_length_mono motifBound
    have wordBits := listCodeEncodeNat_length_mono wordBound
    have columnBits := listCodeEncodeNat_length_mono columnBound
    have targetBits := listCodeEncodeNat_length_mono targetBound
    have motifBitsExplicit :
        (Computability.encodeNat (Encodable.encode motif)).length ≤
          (Computability.encodeNat limit).length := by
      simpa [motifCode] using motifBits
    have targetBitsExplicit :
        (Computability.encodeNat
          (Encodable.encode
            ((Int.ofNat
              (Code.packedColumnPhaseNumerator period phase
                column.val % period), row + verticalOffset) : Cell))).length ≤
          (Computability.encodeNat limit).length := by
      simpa [targetCode, target, x] using targetBits
    have targetPairBits :
        (Computability.encodeNat
          (Nat.pair
            (Encodable.encode
              (Int.ofNat
                (Code.packedColumnPhaseNumerator period phase
                  column.val % period)))
            (Encodable.encode (row + verticalOffset)))).length ≤
          (Computability.encodeNat limit).length := by
      simpa only [Encodable.encode_prod_val] using targetBitsExplicit
    have naturalModCast :
        Int.ofNat
            (Code.packedColumnPhaseNumerator period phase
              column.val % period) =
          (Code.packedColumnPhaseNumerator period phase
              column.val : Int) % (period : Int) := by
      exact Int.natCast_emod
        (Code.packedColumnPhaseNumerator period phase column.val)
        period
    have targetPairBitsInt :
        (Computability.encodeNat
          (Nat.pair
            (Encodable.encode
              ((Code.packedColumnPhaseNumerator period phase
                  column.val : Int) % (period : Int)))
            (Encodable.encode (row + verticalOffset)))).length ≤
          (Computability.encodeNat limit).length := by
      rw [← naturalModCast]
      exact targetPairBits
    simp [values, packedTargetMembershipValues] at inputSpace
    simp only [localUnit, encodedListSpace_cons,
      encodedListSpace_nil] at *
    simp only [Nat.mul_assoc] at targetTotalBound ⊢
    omega
  have getResultScaled :
      getCost 1 [outcome.2.1, outcome.2.2.toNat] ≤
        100000 * ((intOffsetAmount verticalOffset + 1) * unit) :=
    getResultBound.trans (Nat.mul_le_mul_left _ localUnitLeScaled)
  have lookupScaled :
      packedAssignmentLookupCodeCost motif column.val target word ≤
        (intOffsetAmount verticalOffset + 1) * unit :=
    lookupCostBound.trans unitLeScaled
  change
    getCost 1 [outcome.2.1, outcome.2.2.toNat] +
        (packedAssignmentLookupCodeCost motif column.val target word +
          packedTargetMembershipLookupArgumentsCost column verticalOffset
            period phase motif row word) ≤
      1000000000000000000000000000000000000000000000000000000 *
        (intOffsetAmount verticalOffset + 1) * unit
  simp only [Nat.mul_assoc] at lookupArgumentsBound ⊢
  omega

/-- The lookup-input adapter is itself dominated by the complete membership
leaf, so callers that reuse only this prefix inherit the same envelope. -/
theorem packedTargetMembershipLookupArgumentsCost_le_linear
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    packedTargetMembershipLookupArgumentsCost column verticalOffset
        period phase motif row word ≤
      1000000000000000000000000000000000000000000000000000000 *
        (intOffsetAmount verticalOffset + 1) *
        packedTargetMembershipUnit column verticalOffset
          period phase motif row word := by
  calc
    packedTargetMembershipLookupArgumentsCost column verticalOffset
          period phase motif row word ≤
        packedTargetMembershipCost column verticalOffset
          period phase motif row word := by
      simp only [packedTargetMembershipCost,
        packedTargetMembershipLookupCost]
      omega
    _ ≤ _ := packedTargetMembershipCost_le_linear column
      verticalOffset period phase motif row word

end EvaluatorCodeFits

end PartrecToTM2
end Turing
