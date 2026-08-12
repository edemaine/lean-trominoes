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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
