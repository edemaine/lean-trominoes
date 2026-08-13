import LeanTrominoes.PartrecFlatPackedAssignmentAtSpace
import LeanTrominoes.PartrecFlatPackedLookupColumnBound

/-!
# Native-field bounds for five-column flat assignment lookup

All five stages share one envelope containing the original packed word, the
queried column, a constant accumulator-digit ceiling, and the native motif
stream.  This module first relates every one-column scanner call to that common
envelope, then lifts the bound through the exact five-stage certificate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

/-- The digit accumulator starts at zero and grows by at most eight in each of
five passes.  We reserve eight additional units so every one-pass scanner's
internal `digit + 8` envelope fits uniformly. -/
def flatPackedAssignmentEnvelopeFields
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : List Nat :=
  queriedColumn :: flatPackedLookupEnvelopeFields target motif word 48

def flatPackedAssignmentInputUnit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  encodedListSpace
      (flatPackedAssignmentEnvelopeFields motif queriedColumn target word) + 5

theorem flatPackedAssignmentUnitPositive
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    5 ≤ flatPackedAssignmentInputUnit motif queriedColumn target word := by
  simp [flatPackedAssignmentInputUnit]

theorem flatPackedAssignmentLookupUnit_le
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedLookupInputUnit target motif word 48 ≤
      flatPackedAssignmentInputUnit motif queriedColumn target word := by
  simp [flatPackedAssignmentInputUnit,
    flatPackedAssignmentEnvelopeFields, flatPackedLookupInputUnit,
    encodedListSpace_cons]

/-- Any reachable five-pass state fits in the common assignment envelope. -/
theorem flatPackedAssignmentStateSpace_le_unit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat) (found : Bool)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    encodedListSpace
        (Code.flatPackedAssignmentLookupState motif queriedColumn target
          (word, digit, found)) ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  let fields := flatPackedAssignmentEnvelopeFields motif queriedColumn
    target initialWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  have expanded :
      encodedListSpace fields =
        (Computability.encodeNat queriedColumn).length + 1 +
        ((Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat (Encodable.encode target.1)).length + 1 +
        ((Computability.encodeNat (Encodable.encode target.2)).length + 1 +
        ((Computability.encodeNat initialWord).length + 1 +
        ((Computability.encodeNat 48).length + 1 +
          encodedListSpace coordinates))))) := by
    simp [fields, flatPackedAssignmentEnvelopeFields,
      flatPackedLookupEnvelopeFields, coordinates, encodedListSpace_cons]
  have wordBits := encodeNat_length_mono wordBound
  have digitToForty := encodeNat_length_mono digitBound
  have fortyToFortyEight :
      (Computability.encodeNat 40).length ≤
        (Computability.encodeNat 48).length :=
    encodeNat_length_mono (by omega)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;>
    simp [Code.flatPackedAssignmentLookupState,
      flatPackedAssignmentInputUnit, fields, coordinates,
      encodedListSpace_cons, zeroBits, oneBits] at expanded ⊢ <;>
    omega

/-- A one-column scanner whose accumulator is reachable within the five-pass
lookup fits the common assignment unit. -/
theorem flatPackedLookupInputUnit_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupInputUnit target motif word (digit + 8) ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  have wordBits := encodeNat_length_mono wordBound
  have digitEnvelopeBound : digit + 8 ≤ 48 := by omega
  have digitBits := encodeNat_length_mono digitEnvelopeBound
  simp [flatPackedLookupInputUnit, flatPackedLookupEnvelopeFields,
    flatPackedAssignmentInputUnit, flatPackedAssignmentEnvelopeFields,
    encodedListSpace_cons]
  omega

theorem flatPackedLookupSpaceBound_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupSpaceBound target motif word digit ≤
      100000000000000000000000000000000000 *
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 := by
  have unitBound := flatPackedLookupInputUnit_le_assignmentUnit motif
    queriedColumn target initialWord word digit wordBound digitBound
  have squared :
      (flatPackedLookupInputUnit target motif word (digit + 8)) ^ 2 ≤
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 := by
    nlinarith
  simpa only [flatPackedLookupSpaceBound] using
    Nat.mul_le_mul_left 100000000000000000000000000000000000 squared

theorem flatPackedLookupFlatCost_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat) (found selected : Bool)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupFlatCost target selected motif word digit found ≤
      100000000000000000000000000000000000 *
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 :=
  (flatPackedLookupFlatCost_le_quadratic
    target selected motif word digit found).trans
      (flatPackedLookupSpaceBound_le_assignmentUnit motif queriedColumn
        target initialWord word digit wordBound digitBound)

def flatPackedAssignmentScannerBudget
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (initialWord : Nat) : Nat :=
  100000000000000000000000000000000000 *
    (flatPackedAssignmentInputUnit motif queriedColumn target initialWord) ^ 2

theorem flatPackedAssignmentScannerBudgetPositive
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (initialWord : Nat) :
    1 ≤ flatPackedAssignmentScannerBudget
      motif queriedColumn target initialWord := by
  have unit := flatPackedAssignmentUnitPositive
    motif queriedColumn target initialWord
  simp [flatPackedAssignmentScannerBudget]
  nlinarith

theorem flatPackedAssignmentQuerySpace_le_unit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (initialWord : Nat) :
    encodedListSpace [queriedColumn] ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  simp [flatPackedAssignmentInputUnit,
    flatPackedAssignmentEnvelopeFields, encodedListSpace_cons]
  omega

theorem flatPackedAssignmentCurrentColumnSpace_le_unit
    (currentColumn : Nat) (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (initialWord : Nat)
    (columnBound : currentColumn < 5) :
    encodedListSpace [currentColumn] ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  have currentBits := encodeNat_length_mono
    (show currentColumn ≤ 4 by omega)
  have fourBits : (Computability.encodeNat 4).length = 3 := rfl
  rw [fourBits] at currentBits
  have unit := flatPackedAssignmentUnitPositive
    motif queriedColumn target initialWord
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  omega

theorem flatPackedAssignmentColumnSelectedCost_le_budget
    (currentColumn : Nat) (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool)
    (initialWord : Nat) (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 40) :
    flatPackedAssignmentColumnSelectedCost currentColumn motif queriedColumn
        target accumulator ≤
      flatPackedAssignmentScannerBudget motif queriedColumn target
        initialWord := by
  let unit := flatPackedAssignmentInputUnit motif queriedColumn target
    initialWord
  let budget := flatPackedAssignmentScannerBudget motif queriedColumn target
    initialWord
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn target
    accumulator
  have unitPositive : 5 ≤ unit := by
    simpa [unit] using flatPackedAssignmentUnitPositive
      motif queriedColumn target initialWord
  have budgetPositive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentScannerBudgetPositive
      motif queriedColumn target initialWord
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using flatPackedAssignmentStateSpace_le_unit
      motif queriedColumn target initialWord accumulator.1 accumulator.2.1
      accumulator.2.2 wordBound digitBound
  have querySpace : encodedListSpace [queriedColumn] ≤ unit := by
    simpa [unit] using flatPackedAssignmentQuerySpace_le_unit
      motif queriedColumn target initialWord
  have currentSpace : encodedListSpace [currentColumn] ≤ unit := by
    simpa [unit] using flatPackedAssignmentCurrentColumnSpace_le_unit
      currentColumn motif queriedColumn target initialWord columnBound
  have pairSpace : encodedListSpace [queriedColumn, currentColumn] ≤
      2 * unit := flatLookupConsSpace_le_of queriedColumn [currentColumn]
        unit querySpace currentSpace
  have getQueryRaw := listCodeGetCost_le_linear 1 state
  have getQuery : getCost 1 state ≤ 20000 * (unit + 1) :=
    getQueryRaw.trans (by gcongr)
  have zeroState := listCodeZeroCost_le_linear state
  have constant := addConstCost_le currentColumn [0]
  have numeralBound : numeralCost currentColumn state ≤
      1000000 * (unit + 1) := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp only [numeralCost]
    simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits] at constant
    nlinarith
  have arguments := listCodePrependCost_le_of state [queriedColumn]
    [currentColumn] (getCost 1 state) (numeralCost currentColumn state)
    (2 * unit) (stateBound.trans (by omega))
    (querySpace.trans (by omega)) pairSpace
  have argumentsBound :
      prependCost state [queriedColumn] [currentColumn]
          (getCost 1 state) (numeralCost currentColumn state) ≤
        2000000 * (unit + 1) := by
    omega
  have equality := flatLookupNatEqCost_le_budget queriedColumn currentColumn
    unit querySpace currentSpace
  change natEqCost queriedColumn currentColumn +
      prependCost state [queriedColumn] [currentColumn]
        (getCost 1 state) (numeralCost currentColumn state) ≤ budget
  simp only [budget, flatPackedAssignmentScannerBudget]
  nlinarith

/-- The exact native scanner input assembled by one numbered stage fits the
common assignment unit. -/
theorem flatPackedAssignmentScannerInputSpace_le_unit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) (selected : Bool)
    (initialWord : Nat) (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 40) :
    encodedListSpace
        (motif.length :: Code.flatPackedLookupColumnState target
          accumulator.1 accumulator.2.1 accumulator.2.2 selected motif) ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  have scanner := flatPackedLookupCountdownStateSpace_le_unit motif.length
    target motif motif [] accumulator.1 accumulator.2.1 initialWord 48
    accumulator.2.2 selected (by simp) (by rfl) wordBound (by omega)
  exact scanner.trans (flatPackedAssignmentLookupUnit_le
    motif queriedColumn target initialWord)

set_option maxHeartbeats 1000000 in
theorem flatPackedAssignmentColumnInputCost_le_budget
    (currentColumn : Nat) (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool)
    (initialWord : Nat) (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 40) :
    flatPackedAssignmentColumnInputCost currentColumn motif queriedColumn
        target accumulator ≤
      20 * flatPackedAssignmentScannerBudget motif queriedColumn target
        initialWord := by
  let unit := flatPackedAssignmentInputUnit motif queriedColumn target
    initialWord
  let budget := flatPackedAssignmentScannerBudget motif queriedColumn target
    initialWord
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn target
    accumulator
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let selected := (decide (queriedColumn = currentColumn)).toNat
  let out7 := selected :: coordinates
  let out6 := accumulator.2.2.toNat :: out7
  let out5 := accumulator.2.1 :: out6
  let out4 := accumulator.1 :: out5
  let out3 := Encodable.encode target.2 :: out4
  let out2 := Encodable.encode target.1 :: out3
  let scannerInput := motif.length :: out2
  have unitPositive : 5 ≤ unit := by
    simpa [unit] using flatPackedAssignmentUnitPositive
      motif queriedColumn target initialWord
  have budgetPositive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentScannerBudgetPositive
      motif queriedColumn target initialWord
  have overheadBudget : 3 * unit + 2 ≤ budget := by
    simp [budget, flatPackedAssignmentScannerBudget]
    nlinarith
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using flatPackedAssignmentStateSpace_le_unit
      motif queriedColumn target initialWord accumulator.1 accumulator.2.1
      accumulator.2.2 wordBound digitBound
  have scannerInputBound : encodedListSpace scannerInput ≤ unit := by
    simpa [scannerInput, out2, out3, out4, out5, out6, out7,
      coordinates, selected, unit,
      Code.flatPackedLookupColumnState] using
      flatPackedAssignmentScannerInputSpace_le_unit motif queriedColumn
        target accumulator (decide (queriedColumn = currentColumn))
        initialWord wordBound digitBound
  have out7Bound : encodedListSpace out7 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le
      [motif.length, Encodable.encode target.1, Encodable.encode target.2,
        accumulator.1, accumulator.2.1, accumulator.2.2.toNat] out7).trans
      (by simpa [scannerInput, out2, out3, out4, out5, out6] using
        scannerInputBound)
  have out6Bound : encodedListSpace out6 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le
      [motif.length, Encodable.encode target.1, Encodable.encode target.2,
        accumulator.1, accumulator.2.1] out6).trans
      (by simpa [scannerInput, out2, out3, out4, out5] using
        scannerInputBound)
  have out5Bound : encodedListSpace out5 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le
      [motif.length, Encodable.encode target.1, Encodable.encode target.2,
        accumulator.1] out5).trans
      (by simpa [scannerInput, out2, out3, out4] using scannerInputBound)
  have out4Bound : encodedListSpace out4 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le
      [motif.length, Encodable.encode target.1,
        Encodable.encode target.2] out4).trans
      (by simpa [scannerInput, out2, out3] using scannerInputBound)
  have out3Bound : encodedListSpace out3 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le
      [motif.length, Encodable.encode target.1] out3).trans
      (by simpa [scannerInput, out2] using scannerInputBound)
  have out2Bound : encodedListSpace out2 ≤ unit := by
    exact (flatLookupEncodedListSpace_suffix_le [motif.length] out2).trans
      (by simpa [scannerInput] using scannerInputBound)
  have selectedSpace : encodedListSpace [selected] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases selectedTag : decide (queriedColumn = currentColumn) <;>
      simp [selected, selectedTag, encodedListSpace_cons,
        encodedListSpace_nil, zeroBits, oneBits] <;> omega
  have foundSpace : encodedListSpace [accumulator.2.2.toNat] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases accumulator.2.2 <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have wordSpace : encodedListSpace [accumulator.1] ≤ unit := by
    have localBound := flatPackedLookupWordSpace_le_unit target motif
      accumulator.1 initialWord 48 wordBound
    exact localBound.trans (flatPackedAssignmentLookupUnit_le
      motif queriedColumn target initialWord)
  have digitSpace : encodedListSpace [accumulator.2.1] ≤ unit := by
    have localBound := flatPackedLookupDigitSpace_le_unit target motif
      initialWord accumulator.2.1 48 (by omega)
    exact localBound.trans (flatPackedAssignmentLookupUnit_le
      motif queriedColumn target initialWord)
  have targetXSpace : encodedListSpace [Encodable.encode target.1] ≤ unit := by
    have localBound := flatPackedLookupTargetXSpace_le_unit target motif
      initialWord 48
    exact localBound.trans (flatPackedAssignmentLookupUnit_le
      motif queriedColumn target initialWord)
  have targetYSpace : encodedListSpace [Encodable.encode target.2] ≤ unit := by
    have localBound := flatPackedLookupTargetYSpace_le_unit target motif
      initialWord 48
    exact localBound.trans (flatPackedAssignmentLookupUnit_le
      motif queriedColumn target initialWord)
  have lengthSpace : encodedListSpace [motif.length] ≤ unit := by
    have localBound := flatPackedLookupCountSpace_le_unit motif.length target
      motif initialWord 48 (by rfl)
    exact localBound.trans (flatPackedAssignmentLookupUnit_le
      motif queriedColumn target initialWord)
  have selectedCost := flatPackedAssignmentColumnSelectedCost_le_budget
    currentColumn motif queriedColumn target accumulator initialWord
    columnBound wordBound digitBound
  have selectedBudget :
      flatPackedAssignmentColumnSelectedCost currentColumn motif queriedColumn
        target accumulator ≤ budget := by simpa [budget] using selectedCost
  have get0Raw := listCodeGetCost_le_linear 0 state
  have get2Raw := listCodeGetCost_le_linear 2 state
  have get3Raw := listCodeGetCost_le_linear 3 state
  have get4Raw := listCodeGetCost_le_linear 4 state
  have get5Raw := listCodeGetCost_le_linear 5 state
  have get6Raw := listCodeGetCost_le_linear 6 state
  have drop7Raw := flatLookupDropCost_le_linear 7 state
  have get0 : getCost 0 state ≤ budget :=
    get0Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get2 : getCost 2 state ≤ budget :=
    get2Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get3 : getCost 3 state ≤ budget :=
    get3Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get4 : getCost 4 state ≤ budget :=
    get4Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get5 : getCost 5 state ≤ budget :=
    get5Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get6 : getCost 6 state ≤ budget :=
    get6Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have drop7 : dropCost 7 state ≤ budget :=
    drop7Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  let cost7 := prependCost state [selected] coordinates
    (flatPackedAssignmentColumnSelectedCost currentColumn motif queriedColumn
      target accumulator) (dropCost 7 state)
  let cost6 := prependCost state [accumulator.2.2.toNat] out7
    (getCost 6 state) cost7
  let cost5 := prependCost state [accumulator.2.1] out6
    (getCost 5 state) cost6
  let cost4 := prependCost state [accumulator.1] out5
    (getCost 4 state) cost5
  let cost3 := prependCost state [Encodable.encode target.2] out4
    (getCost 3 state) cost4
  let cost2 := prependCost state [Encodable.encode target.1] out3
    (getCost 2 state) cost3
  let cost0 := prependCost state [motif.length] out2
    (getCost 0 state) cost2
  have estimate7 := listCodePrependCost_le_of state [selected] coordinates
    (flatPackedAssignmentColumnSelectedCost currentColumn motif queriedColumn
      target accumulator) (dropCost 7 state) unit
    stateBound selectedSpace out7Bound
  have bound7 : cost7 ≤ 3 * budget := by
    simp only [cost7]
    omega
  have estimate6 := listCodePrependCost_le_of state
    [accumulator.2.2.toNat] out7 (getCost 6 state) cost7 unit
    stateBound foundSpace out6Bound
  have bound6 : cost6 ≤ 5 * budget := by
    simp only [cost6]
    omega
  have estimate5 := listCodePrependCost_le_of state [accumulator.2.1]
    out6 (getCost 5 state) cost6 unit stateBound digitSpace out5Bound
  have bound5 : cost5 ≤ 7 * budget := by
    simp only [cost5]
    omega
  have estimate4 := listCodePrependCost_le_of state [accumulator.1]
    out5 (getCost 4 state) cost5 unit stateBound wordSpace out4Bound
  have bound4 : cost4 ≤ 9 * budget := by
    simp only [cost4]
    omega
  have estimate3 := listCodePrependCost_le_of state
    [Encodable.encode target.2] out4 (getCost 3 state) cost4 unit
    stateBound targetYSpace out3Bound
  have bound3 : cost3 ≤ 11 * budget := by
    simp only [cost3]
    omega
  have estimate2 := listCodePrependCost_le_of state
    [Encodable.encode target.1] out3 (getCost 2 state) cost3 unit
    stateBound targetXSpace out2Bound
  have bound2 : cost2 ≤ 13 * budget := by
    simp only [cost2]
    omega
  have estimate0 := listCodePrependCost_le_of state [motif.length]
    out2 (getCost 0 state) cost2 unit stateBound lengthSpace scannerInputBound
  have bound0 : cost0 ≤ 20 * budget := by
    simp only [cost0]
    omega
  simpa only [flatPackedAssignmentColumnInputCost, state, coordinates,
    selected, out7, out6, out5, out4, out3, out2, cost7, cost6,
    cost5, cost4, cost3, cost2, cost0, budget] using bound0

theorem flatPackedAssignmentColumnCallCost_le_budget
    (currentColumn : Nat) (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool)
    (initialWord : Nat) (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 40) :
    flatPackedAssignmentColumnCallCost currentColumn motif queriedColumn
        target accumulator ≤
      21 * flatPackedAssignmentScannerBudget motif queriedColumn target
        initialWord := by
  have scanner := flatPackedLookupFlatCost_le_assignmentUnit motif
    queriedColumn target initialWord accumulator.1 accumulator.2.1
    accumulator.2.2 (decide (queriedColumn = currentColumn))
    wordBound digitBound
  have scannerBudget :
      flatPackedLookupFlatCost target
          (decide (queriedColumn = currentColumn)) motif accumulator.1
          accumulator.2.1 accumulator.2.2 ≤
        flatPackedAssignmentScannerBudget motif queriedColumn target
          initialWord := by
    simpa [flatPackedAssignmentScannerBudget] using scanner
  have input := flatPackedAssignmentColumnInputCost_le_budget currentColumn
    motif queriedColumn target accumulator initialWord columnBound
    wordBound digitBound
  simp only [flatPackedAssignmentColumnCallCost]
  omega

theorem flatPackedAssignmentColumnResultFieldCost_le_budget
    (currentColumn : Nat) (outputField : Fin 3)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool)
    (initialWord : Nat) (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 40) :
    flatPackedAssignmentColumnResultFieldCost currentColumn outputField
        motif queriedColumn target accumulator ≤
      1000000 * flatPackedAssignmentScannerBudget motif queriedColumn target
        initialWord := by
  let budget := flatPackedAssignmentScannerBudget motif queriedColumn target
    initialWord
  let selected := decide (queriedColumn = currentColumn)
  let result := Code.flatPackedLookupColumnProcess target selected motif
    accumulator.1 accumulator.2.1 accumulator.2.2
  have budgetPositive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentScannerBudgetPositive
      motif queriedColumn target initialWord
  have scannerFit := flatPackedLookupFlat target selected motif
    accumulator.1 accumulator.2.1 accumulator.2.2
  have scannerCost := flatPackedLookupFlatCost_le_assignmentUnit motif
    queriedColumn target initialWord accumulator.1 accumulator.2.1
    accumulator.2.2 selected wordBound digitBound
  have resultSpace : encodedListSpace result ≤ budget := by
    have output := scannerFit.output_space
    exact output.trans (by simpa [budget,
      flatPackedAssignmentScannerBudget] using scannerCost)
  have indexBound : outputField.val + 2 ≤ 4 := by omega
  have projectionRaw := listCodeGetCost_le_linear (outputField.val + 2) result
  have projection : getCost (outputField.val + 2) result ≤
      100000 * budget := by
    have coefficient : 10000 * (outputField.val + 2 + 1) ≤ 50000 := by
      omega
    have space : encodedListSpace result + 1 ≤ 2 * budget := by omega
    exact projectionRaw.trans (by
      calc
        (10000 * (outputField.val + 2 + 1)) *
            (encodedListSpace result + 1) ≤
          50000 * (2 * budget) := Nat.mul_le_mul coefficient space
        _ ≤ 100000 * budget := by ring_nf; omega)
  have call := flatPackedAssignmentColumnCallCost_le_budget currentColumn
    motif queriedColumn target accumulator initialWord columnBound
    wordBound digitBound
  change getCost (outputField.val + 2) result +
      flatPackedAssignmentColumnCallCost currentColumn motif queriedColumn
        target accumulator ≤ 1000000 * budget
  omega

set_option maxHeartbeats 1000000 in
theorem flatPackedAssignmentColumnStageCost_le_budget
    (currentColumn : Nat) (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool)
    (initialWord : Nat) (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ 32) :
    flatPackedAssignmentColumnStageCost currentColumn motif queriedColumn
        target accumulator ≤
      10000000 * flatPackedAssignmentScannerBudget motif queriedColumn target
        initialWord := by
  let unit := flatPackedAssignmentInputUnit motif queriedColumn target
    initialWord
  let budget := flatPackedAssignmentScannerBudget motif queriedColumn target
    initialWord
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn target
    accumulator
  let next := Code.packedAssignmentLookupApplyColumn currentColumn motif
    queriedColumn target accumulator
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let out7 := next.2.2.toNat :: coordinates
  let out6 := next.2.1 :: out7
  let out5 := next.1 :: out6
  let out3 := Encodable.encode target.2 :: out5
  let out2 := Encodable.encode target.1 :: out3
  let out1 := queriedColumn :: out2
  let finalState := motif.length :: out1
  have unitPositive : 5 ≤ unit := by
    simpa [unit] using flatPackedAssignmentUnitPositive
      motif queriedColumn target initialWord
  have budgetPositive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentScannerBudgetPositive
      motif queriedColumn target initialWord
  have overheadBudget : 3 * unit + 2 ≤ budget := by
    simp [budget, flatPackedAssignmentScannerBudget]
    nlinarith
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using flatPackedAssignmentStateSpace_le_unit
      motif queriedColumn target initialWord accumulator.1 accumulator.2.1
      accumulator.2.2 wordBound (by omega)
  have nextWord : next.1 ≤ accumulator.1 := by
    simpa [next, Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = currentColumn)) motif accumulator.1
        accumulator.2.1 accumulator.2.2
  have nextDigit : next.2.1 ≤ accumulator.2.1 + 8 := by
    simpa [next, Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = currentColumn)) motif accumulator.1
        accumulator.2.1 accumulator.2.2
  have nextWordBound : next.1 ≤ initialWord := nextWord.trans wordBound
  have nextDigitBound : next.2.1 ≤ 40 := by omega
  have finalBound : encodedListSpace finalState ≤ unit := by
    simpa [finalState, out1, out2, out3, out5, out6, out7,
      coordinates, next, unit,
      Code.flatPackedAssignmentLookupState] using
      flatPackedAssignmentStateSpace_le_unit motif queriedColumn target
        initialWord next.1 next.2.1 next.2.2 nextWordBound nextDigitBound
  have out7Bound : encodedListSpace out7 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le
      [motif.length, queriedColumn, Encodable.encode target.1,
        Encodable.encode target.2, next.1, next.2.1] out7).trans
      (by simpa [finalState, out1, out2, out3, out5, out6] using finalBound)
  have out6Bound : encodedListSpace out6 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le
      [motif.length, queriedColumn, Encodable.encode target.1,
        Encodable.encode target.2, next.1] out6).trans
      (by simpa [finalState, out1, out2, out3, out5] using finalBound)
  have out5Bound : encodedListSpace out5 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le
      [motif.length, queriedColumn, Encodable.encode target.1,
        Encodable.encode target.2] out5).trans
      (by simpa [finalState, out1, out2, out3] using finalBound)
  have out3Bound : encodedListSpace out3 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le
      [motif.length, queriedColumn, Encodable.encode target.1] out3).trans
      (by simpa [finalState, out1, out2] using finalBound)
  have out2Bound : encodedListSpace out2 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le
      [motif.length, queriedColumn] out2).trans
      (by simpa [finalState, out1] using finalBound)
  have out1Bound : encodedListSpace out1 ≤ unit :=
    (flatLookupEncodedListSpace_suffix_le [motif.length] out1).trans
      (by simpa [finalState] using finalBound)
  have nextFoundSpace : encodedListSpace [next.2.2.toNat] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [next.2.2.toNat]
      coordinates).trans out7Bound
  have nextDigitSpace : encodedListSpace [next.2.1] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [next.2.1] out7).trans out6Bound
  have nextWordSpace : encodedListSpace [next.1] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [next.1] out6).trans out5Bound
  have targetYSpace : encodedListSpace [Encodable.encode target.2] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [Encodable.encode target.2]
      out5).trans out3Bound
  have targetXSpace : encodedListSpace [Encodable.encode target.1] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [Encodable.encode target.1]
      out3).trans out2Bound
  have querySpace : encodedListSpace [queriedColumn] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [queriedColumn] out2).trans out1Bound
  have lengthSpace : encodedListSpace [motif.length] ≤ unit :=
    (flatLookupEncodedListSpace_prefix_le [motif.length] out1).trans finalBound
  have result0 := flatPackedAssignmentColumnResultFieldCost_le_budget
    currentColumn (0 : Fin 3) motif queriedColumn target accumulator
    initialWord columnBound wordBound (by omega)
  have result1 := flatPackedAssignmentColumnResultFieldCost_le_budget
    currentColumn (1 : Fin 3) motif queriedColumn target accumulator
    initialWord columnBound wordBound (by omega)
  have result2 := flatPackedAssignmentColumnResultFieldCost_le_budget
    currentColumn (2 : Fin 3) motif queriedColumn target accumulator
    initialWord columnBound wordBound (by omega)
  have drop7Raw := flatLookupDropCost_le_linear 7 state
  have get0Raw := listCodeGetCost_le_linear 0 state
  have get1Raw := listCodeGetCost_le_linear 1 state
  have get2Raw := listCodeGetCost_le_linear 2 state
  have get3Raw := listCodeGetCost_le_linear 3 state
  have drop7 : dropCost 7 state ≤ budget :=
    drop7Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get0 : getCost 0 state ≤ budget :=
    get0Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get1 : getCost 1 state ≤ budget :=
    get1Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get2 : getCost 2 state ≤ budget :=
    get2Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  have get3 : getCost 3 state ≤ budget :=
    get3Raw.trans (by simp [budget, flatPackedAssignmentScannerBudget]; nlinarith)
  let cost7 := prependCost state [next.2.2.toNat] coordinates
    (flatPackedAssignmentColumnResultFieldCost currentColumn (2 : Fin 3)
      motif queriedColumn target accumulator) (dropCost 7 state)
  let cost6 := prependCost state [next.2.1] out7
    (flatPackedAssignmentColumnResultFieldCost currentColumn (1 : Fin 3)
      motif queriedColumn target accumulator) cost7
  let cost5 := prependCost state [next.1] out6
    (flatPackedAssignmentColumnResultFieldCost currentColumn (0 : Fin 3)
      motif queriedColumn target accumulator) cost6
  let cost3 := prependCost state [Encodable.encode target.2] out5
    (getCost 3 state) cost5
  let cost2 := prependCost state [Encodable.encode target.1] out3
    (getCost 2 state) cost3
  let cost1 := prependCost state [queriedColumn] out2
    (getCost 1 state) cost2
  let cost0 := prependCost state [motif.length] out1
    (getCost 0 state) cost1
  have estimate7 := listCodePrependCost_le_of state [next.2.2.toNat]
    coordinates
    (flatPackedAssignmentColumnResultFieldCost currentColumn (2 : Fin 3)
      motif queriedColumn target accumulator) (dropCost 7 state) unit
    stateBound nextFoundSpace out7Bound
  have bound7 : cost7 ≤ 1000002 * budget := by
    simp only [cost7]
    omega
  have estimate6 := listCodePrependCost_le_of state [next.2.1] out7
    (flatPackedAssignmentColumnResultFieldCost currentColumn (1 : Fin 3)
      motif queriedColumn target accumulator) cost7 unit
    stateBound nextDigitSpace out6Bound
  have bound6 : cost6 ≤ 2000004 * budget := by
    simp only [cost6]
    omega
  have estimate5 := listCodePrependCost_le_of state [next.1] out6
    (flatPackedAssignmentColumnResultFieldCost currentColumn (0 : Fin 3)
      motif queriedColumn target accumulator) cost6 unit
    stateBound nextWordSpace out5Bound
  have bound5 : cost5 ≤ 3000006 * budget := by
    simp only [cost5]
    omega
  have estimate3 := listCodePrependCost_le_of state
    [Encodable.encode target.2] out5 (getCost 3 state) cost5 unit
    stateBound targetYSpace out3Bound
  have bound3 : cost3 ≤ 3000008 * budget := by
    simp only [cost3]
    omega
  have estimate2 := listCodePrependCost_le_of state
    [Encodable.encode target.1] out3 (getCost 2 state) cost3 unit
    stateBound targetXSpace out2Bound
  have bound2 : cost2 ≤ 3000010 * budget := by
    simp only [cost2]
    omega
  have estimate1 := listCodePrependCost_le_of state [queriedColumn]
    out2 (getCost 1 state) cost2 unit stateBound querySpace out1Bound
  have bound1 : cost1 ≤ 3000012 * budget := by
    simp only [cost1]
    omega
  have estimate0 := listCodePrependCost_le_of state [motif.length]
    out1 (getCost 0 state) cost1 unit stateBound lengthSpace finalBound
  have bound0 : cost0 ≤ 10000000 * budget := by
    simp only [cost0]
    omega
  simpa only [flatPackedAssignmentColumnStageCost, state, next,
    coordinates, out7, out6, out5, out3, out2, out1,
    cost7, cost6, cost5, cost3, cost2, cost1, cost0, budget] using bound0

set_option maxHeartbeats 800000 in
theorem flatPackedAssignmentLookupStagesCost_le_budget
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupStagesCost motif queriedColumn target word ≤
      50000000 * flatPackedAssignmentScannerBudget motif queriedColumn target
        word := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first := Code.packedAssignmentLookupApplyColumn
    0 motif queriedColumn target initial
  let second := Code.packedAssignmentLookupApplyColumn
    1 motif queriedColumn target first
  let third := Code.packedAssignmentLookupApplyColumn
    2 motif queriedColumn target second
  let fourth := Code.packedAssignmentLookupApplyColumn
    3 motif queriedColumn target third
  let budget := flatPackedAssignmentScannerBudget motif queriedColumn target
    word
  have firstWord : first.1 ≤ word := by
    simpa [first, initial, Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = 0)) motif word 0 false
  have firstDigit : first.2.1 ≤ 8 := by
    simpa [first, initial, Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = 0)) motif word 0 false
  have secondWord : second.1 ≤ word := by
    have step := Code.packedLookupColumnOutcome_word_le target
      (decide (queriedColumn = 1)) motif first.1 first.2.1 first.2.2
    have applied : second.1 ≤ first.1 := by
      simpa [second, Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans firstWord
  have secondDigit : second.2.1 ≤ 16 := by
    have step := Code.packedLookupColumnOutcome_digit_le target
      (decide (queriedColumn = 1)) motif first.1 first.2.1 first.2.2
    have applied : second.2.1 ≤ first.2.1 + 8 := by
      simpa [second, Code.packedAssignmentLookupApplyColumn] using step
    omega
  have thirdWord : third.1 ≤ word := by
    have step := Code.packedLookupColumnOutcome_word_le target
      (decide (queriedColumn = 2)) motif second.1 second.2.1 second.2.2
    have applied : third.1 ≤ second.1 := by
      simpa [third, Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans secondWord
  have thirdDigit : third.2.1 ≤ 24 := by
    have step := Code.packedLookupColumnOutcome_digit_le target
      (decide (queriedColumn = 2)) motif second.1 second.2.1 second.2.2
    have applied : third.2.1 ≤ second.2.1 + 8 := by
      simpa [third, Code.packedAssignmentLookupApplyColumn] using step
    omega
  have fourthWord : fourth.1 ≤ word := by
    have step := Code.packedLookupColumnOutcome_word_le target
      (decide (queriedColumn = 3)) motif third.1 third.2.1 third.2.2
    have applied : fourth.1 ≤ third.1 := by
      simpa [fourth, Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans thirdWord
  have fourthDigit : fourth.2.1 ≤ 32 := by
    have step := Code.packedLookupColumnOutcome_digit_le target
      (decide (queriedColumn = 3)) motif third.1 third.2.1 third.2.2
    have applied : fourth.2.1 ≤ third.2.1 + 8 := by
      simpa [fourth, Code.packedAssignmentLookupApplyColumn] using step
    omega
  have stage0 :
      flatPackedAssignmentColumnStageCost 0 motif queriedColumn target
          initial ≤ 10000000 * budget := by
    simpa [budget] using flatPackedAssignmentColumnStageCost_le_budget
      0 motif queriedColumn target initial word (by omega)
      (by simp [initial]) (by simp [initial])
  have stage1 :
      flatPackedAssignmentColumnStageCost 1 motif queriedColumn target
          first ≤ 10000000 * budget := by
    simpa [budget] using flatPackedAssignmentColumnStageCost_le_budget
      1 motif queriedColumn target first word (by omega) firstWord (by omega)
  have stage2 :
      flatPackedAssignmentColumnStageCost 2 motif queriedColumn target
          second ≤ 10000000 * budget := by
    simpa [budget] using flatPackedAssignmentColumnStageCost_le_budget
      2 motif queriedColumn target second word (by omega) secondWord (by omega)
  have stage3 :
      flatPackedAssignmentColumnStageCost 3 motif queriedColumn target
          third ≤ 10000000 * budget := by
    simpa [budget] using flatPackedAssignmentColumnStageCost_le_budget
      3 motif queriedColumn target third word (by omega) thirdWord (by omega)
  have stage4 :
      flatPackedAssignmentColumnStageCost 4 motif queriedColumn target
          fourth ≤ 10000000 * budget := by
    simpa [budget] using flatPackedAssignmentColumnStageCost_le_budget
      4 motif queriedColumn target fourth word (by omega) fourthWord (by omega)
  have sumBound :
      flatPackedAssignmentColumnStageCost 4 motif queriedColumn target fourth +
        (flatPackedAssignmentColumnStageCost 3 motif queriedColumn target third +
          (flatPackedAssignmentColumnStageCost 2 motif queriedColumn target
              second +
            (flatPackedAssignmentColumnStageCost 1 motif queriedColumn target
                first +
              flatPackedAssignmentColumnStageCost 0 motif queriedColumn target
                initial))) ≤ 50000000 * budget := by
    omega
  simpa only [flatPackedAssignmentLookupStagesCost, initial, first, second,
    third, fourth, budget] using sumBound

end EvaluatorCodeFits
end PartrecToTM2
end Turing
