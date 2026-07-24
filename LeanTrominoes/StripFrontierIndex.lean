import LeanTrominoes.StripFrontierEncoding
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Arithmetic indices for sparse strip frontiers

The raw representation avoids an input-dependent state type, but a direct
enumeration of all raw words is still exponentially large.  This file ranks
each nine-symbol assignment word as a base-nine natural number and combines
that rank with the horizontal phase.  Conversely, a bounded natural index is
decoded on demand, without constructing the list of all states.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

/-- The position of an assignment symbol in the canonical nine-symbol list. -/
def assignmentDigit (state : Option SquareSymmetry) : Nat :=
  TrominoAssignment.assignmentStateList.idxOf state

/-- Interpret a base-nine digit as an assignment symbol. -/
def assignmentOfDigit (digit : Nat) : Option SquareSymmetry :=
  TrominoAssignment.assignmentStateList.getD digit none

@[simp]
theorem length_assignmentStateList :
    TrominoAssignment.assignmentStateList.length = 9 := by
  native_decide

theorem assignmentDigit_lt (state : Option SquareSymmetry) :
    assignmentDigit state < 9 := by
  rw [← length_assignmentStateList]
  exact List.idxOf_lt_length_of_mem
    (TrominoAssignment.mem_assignmentStateList state)

@[simp]
theorem assignmentOfDigit_assignmentDigit
    (state : Option SquareSymmetry) :
    assignmentOfDigit (assignmentDigit state) = state := by
  unfold assignmentOfDigit assignmentDigit
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_idxOf
      (TrominoAssignment.mem_assignmentStateList state)]
  rfl

@[simp]
theorem map_assignmentOfDigit_map_assignmentDigit
    (assignment : List (Option SquareSymmetry)) :
    (assignment.map assignmentDigit).map assignmentOfDigit =
      assignment := by
  induction assignment with
  | nil => rfl
  | cons state assignment induction =>
      simp [induction]

/-- Rank a fixed-length assignment word as a base-nine number. -/
def encodeAssignment (assignment : List (Option SquareSymmetry)) : Nat :=
  Nat.ofDigits 9 (assignment.map assignmentDigit)

/-- Read one base-nine digit at a little-endian position. -/
def assignmentDigitAt (code position : Nat) : Nat :=
  code / 9 ^ position % 9

/-- Decode exactly `length` little-endian base-nine digits.  This explicit
`List.range` presentation is convenient for primitive-recursion proofs and
allocates only the one polynomial-length frontier word. -/
def decodeAssignment (length code : Nat) :
    List (Option SquareSymmetry) :=
  (List.range length).map fun position =>
    assignmentOfDigit (assignmentDigitAt code position)

theorem encodeAssignment_lt (assignment : List (Option SquareSymmetry)) :
    encodeAssignment assignment < 9 ^ assignment.length := by
  unfold encodeAssignment
  have digitBound :
      ∀ digit ∈ assignment.map assignmentDigit, digit < 9 := by
    intro digit digitMem
    obtain ⟨state, _, rfl⟩ := List.mem_map.mp digitMem
    exact assignmentDigit_lt state
  simpa using
    (Nat.ofDigits_lt_base_pow_length (by omega) digitBound)

@[simp]
theorem decodeAssignment_encodeAssignment
    (assignment : List (Option SquareSymmetry)) :
    decodeAssignment assignment.length (encodeAssignment assignment) =
      assignment := by
  let digits := assignment.map assignmentDigit
  have digitBound : ∀ digit ∈ digits, digit < 9 := by
    intro digit digitMem
    obtain ⟨state, _, rfl⟩ := List.mem_map.mp digitMem
    exact assignmentDigit_lt state
  apply List.ext_get
  · simp [decodeAssignment]
  · intro position leftBound rightBound
    simp [decodeAssignment]
    change assignmentOfDigit
      (Nat.ofDigits 9 digits / 9 ^ position % 9) =
        assignment[position]
    rw [Nat.ofDigits_div_pow_eq_ofDigits_drop
      position (by omega) digits digitBound]
    rw [Nat.ofDigits_mod_eq_head!]
    have headEq :
        (digits.drop position).head! =
          assignmentDigit assignment[position] := by
      simp [List.head!_eq_head?_getD, List.head?_eq_getElem?,
        digits, rightBound]
    rw [headEq, Nat.mod_eq_of_lt
      (assignmentDigit_lt assignment[position])]
    exact assignmentOfDigit_assignmentDigit assignment[position]

@[simp]
theorem length_decodeAssignment (length code : Nat) :
    (decodeAssignment length code).length = length := by
  simp [decodeAssignment]

/-- Number of arithmetic indices for a strip's sparse frontier states. -/
def indexCount (periodicStrip : PeriodicStrip) : Nat :=
  periodicStrip.period *
    9 ^ (assignmentKeys periodicStrip).length

theorem indexCount_eq (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip =
      periodicStrip.period *
        9 ^ (5 * periodicStrip.motif.toFinset.card) := by
  simp [indexCount]

/-- Rank a raw frontier by phase, then by its base-nine assignment word. -/
def index (periodicStrip : PeriodicStrip) (raw : RawWindowState) : Nat :=
  raw.phase +
    periodicStrip.period * encodeAssignment raw.assignment

theorem index_lt_indexCount {periodicStrip : PeriodicStrip}
    {raw : RawWindowState} (valid : raw.IsValid periodicStrip) :
    index periodicStrip raw < indexCount periodicStrip := by
  have codeBound :=
    encodeAssignment_lt raw.assignment
  rw [valid.2] at codeBound
  have phaseStep :
      raw.phase +
          periodicStrip.period * encodeAssignment raw.assignment <
        periodicStrip.period +
          periodicStrip.period * encodeAssignment raw.assignment :=
    Nat.add_lt_add_right valid.1 _
  have codeStep :
      periodicStrip.period +
          periodicStrip.period * encodeAssignment raw.assignment ≤
        periodicStrip.period *
          9 ^ (assignmentKeys periodicStrip).length := by
    calc
      periodicStrip.period +
            periodicStrip.period * encodeAssignment raw.assignment =
          periodicStrip.period * encodeAssignment raw.assignment +
            periodicStrip.period := Nat.add_comm _ _
      _ = periodicStrip.period *
            (encodeAssignment raw.assignment + 1) := by
          rw [Nat.mul_succ]
      _ ≤ periodicStrip.period *
            9 ^ (assignmentKeys periodicStrip).length :=
          Nat.mul_le_mul_left _
            (Nat.succ_le_of_lt codeBound)
  exact phaseStep.trans_le codeStep

/-- Decode one arithmetic state index.  The intended domain is
`index < indexCount periodicStrip`; outside that range the word need not have
the canonical length. -/
def ofIndex (periodicStrip : PeriodicStrip) (stateIndex : Nat) :
    RawWindowState where
  phase := stateIndex % periodicStrip.period
  assignment :=
    decodeAssignment (assignmentKeys periodicStrip).length
      (stateIndex / periodicStrip.period)

theorem ofIndex_isValid {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period) {stateIndex : Nat}
    (_indexBound : stateIndex < indexCount periodicStrip) :
    (ofIndex periodicStrip stateIndex).IsValid periodicStrip := by
  constructor
  · exact Nat.mod_lt _ periodPositive
  · exact length_decodeAssignment _ _

@[simp]
theorem ofIndex_index {periodicStrip : PeriodicStrip}
    {raw : RawWindowState} (valid : raw.IsValid periodicStrip) :
    ofIndex periodicStrip (index periodicStrip raw) = raw := by
  have periodPositive : 0 < periodicStrip.period :=
    Nat.zero_lt_of_lt valid.1
  rcases raw with ⟨phase, assignment⟩
  unfold ofIndex index
  congr 1
  · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt valid.1]
  · have lengthEq :
        (assignmentKeys periodicStrip).length = assignment.length :=
      valid.2.symm
    rw [Nat.add_mul_div_left phase
      (encodeAssignment assignment) periodPositive]
    rw [Nat.div_eq_of_lt valid.1, Nat.zero_add, lengthEq]
    exact decodeAssignment_encodeAssignment assignment

/-- The arithmetic indices are complete for semantic frontier states. -/
theorem exists_index_decode_eq {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    ∃ stateIndex < indexCount periodicStrip,
      decode periodicStrip (ofIndex periodicStrip stateIndex) = some state := by
  let raw := encode state
  refine ⟨index periodicStrip raw, index_lt_indexCount (encode_isValid state),
    ?_⟩
  rw [ofIndex_index (encode_isValid state)]
  exact decode_encode state

end RawWindowState
end PeriodicStrip
end LeanTrominoes
