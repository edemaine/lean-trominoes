import LeanTrominoes.ComputableSearch
import LeanTrominoes.StripFrontier

/-!
# Uniform encodings of sparse strip frontiers

`WindowState periodicStrip` is the convenient semantic representation of a
strip frontier, but its type depends on the input strip and its assignment is
a function.  This file gives the same data a uniform, list-based
representation.  The five window columns are ordered first, and within each
column the cells are ordered by the computable list
`periodicStrip.motif.dedup`.

The raw representation is what a space-bounded evaluator can store and
generate on demand.  In particular, its assignment word has exactly
`5 * periodicStrip.motif.toFinset.card` symbols over the existing nine-symbol
assignment alphabet.
-/

namespace LeanTrominoes
namespace PeriodicStrip

/-- A strip-frontier state represented without an input-dependent type. -/
structure RawWindowState where
  phase : Nat
  assignment : List (Option SquareSymmetry)
  deriving DecidableEq, Repr

namespace RawWindowState

/-- The canonical list of distinct motif cells. -/
def motifCells (periodicStrip : PeriodicStrip) : List Cell :=
  periodicStrip.motif.dedup

@[simp]
theorem length_motifCells (periodicStrip : PeriodicStrip) :
    (motifCells periodicStrip).length =
      periodicStrip.motif.toFinset.card := by
  simpa [motifCells] using
    (List.card_toFinset periodicStrip.motif).symm

@[simp]
theorem mem_motifCells (periodicStrip : PeriodicStrip) (cell : Cell) :
    cell ∈ motifCells periodicStrip ↔
      cell ∈ periodicStrip.motif.toFinset := by
  simp [motifCells]

/-- Canonical order of the five copies of the distinct motif cells. -/
def assignmentKeys (periodicStrip : PeriodicStrip) :
    List (WindowColumn × Cell) :=
  (List.finRange 5).flatMap fun column =>
    (motifCells periodicStrip).map fun cell => (column, cell)

@[simp]
theorem length_assignmentKeys (periodicStrip : PeriodicStrip) :
    (assignmentKeys periodicStrip).length =
      5 * periodicStrip.motif.toFinset.card := by
  simp [assignmentKeys]
  omega

@[simp]
theorem mem_assignmentKeys (periodicStrip : PeriodicStrip)
    (column : WindowColumn) (base : periodicStrip.MotifCell) :
    (column, base.val) ∈ assignmentKeys periodicStrip := by
  simp only [assignmentKeys, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨column, ⟨base.val,
    (mem_motifCells periodicStrip base.val).mpr base.property, rfl⟩⟩

/-- A raw state has the phase and word length prescribed by the input strip. -/
def IsValid (periodicStrip : PeriodicStrip) (raw : RawWindowState) : Prop :=
  raw.phase < periodicStrip.period ∧
    raw.assignment.length = (assignmentKeys periodicStrip).length

instance (periodicStrip : PeriodicStrip) (raw : RawWindowState) :
    Decidable (raw.IsValid periodicStrip) := by
  unfold IsValid
  infer_instance

/-- Read one semantic assignment value from a raw assignment word. -/
def assignmentAt (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (column : WindowColumn) (base : periodicStrip.MotifCell) :
    Option SquareSymmetry :=
  raw.assignment.getD
    ((assignmentKeys periodicStrip).idxOf (column, base.val)) none

/-- Decode a well-sized raw state into the dependent semantic state type. -/
def decode (periodicStrip : PeriodicStrip) (raw : RawWindowState) :
    Option (WindowState periodicStrip) :=
  if valid : raw.IsValid periodicStrip then
    some
      { phase := ⟨raw.phase, valid.1⟩
        assignment := raw.assignmentAt periodicStrip }
  else
    none

/-- Read a semantic assignment at an untyped motif cell. -/
def semanticAssignmentAtCell {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) (key : WindowColumn × Cell) :
    Option SquareSymmetry :=
  if member : key.2 ∈ periodicStrip.motif.toFinset then
    state.assignment key.1 ⟨key.2, member⟩
  else
    none

@[simp]
theorem semanticAssignmentAtCell_base {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) (column : WindowColumn)
    (base : periodicStrip.MotifCell) :
    semanticAssignmentAtCell state (column, base.val) =
      state.assignment column base := by
  simp [semanticAssignmentAtCell]

/-- Encode a semantic state in the canonical raw representation. -/
def encode {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : RawWindowState where
  phase := state.phase.val
  assignment :=
    (assignmentKeys periodicStrip).map (semanticAssignmentAtCell state)

theorem encode_isValid {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    (encode state).IsValid periodicStrip := by
  constructor
  · exact state.phase.isLt
  · simp [encode]

private theorem getD_map_idxOf_of_mem {α β : Type*} [BEq α] [LawfulBEq α]
    (keys : List α) (value : α → β) (default : β) {key : α}
    (member : key ∈ keys) :
    (keys.map value).getD (keys.idxOf key) default = value key := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf member]
  rfl

@[simp]
theorem assignmentAt_encode {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) (column : WindowColumn)
    (base : periodicStrip.MotifCell) :
    (encode state).assignmentAt periodicStrip column base =
      state.assignment column base := by
  change
    ((assignmentKeys periodicStrip).map
      (semanticAssignmentAtCell state)).getD
        ((assignmentKeys periodicStrip).idxOf (column, base.val)) none =
      state.assignment column base
  calc
    _ = semanticAssignmentAtCell state (column, base.val) :=
      getD_map_idxOf_of_mem _ _ _
        (mem_assignmentKeys periodicStrip column base)
    _ = state.assignment column base :=
      semanticAssignmentAtCell_base state column base

@[simp]
theorem decode_encode {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    decode periodicStrip (encode state) = some state := by
  rw [decode, dif_pos (encode_isValid state)]
  congr 1
  cases state with
  | mk phase assignment =>
      congr 1
      funext column base
      exact assignmentAt_encode ⟨phase, assignment⟩ column base

/-- All canonically sized raw frontier states for an input strip. -/
def all (periodicStrip : PeriodicStrip) : List RawWindowState :=
  (List.range periodicStrip.period).flatMap fun phase =>
    (LeanWang.words TrominoAssignment.assignmentStateList
      (assignmentKeys periodicStrip).length).map fun assignment =>
        ⟨phase, assignment⟩

@[simp]
theorem mem_all_iff (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) :
    raw ∈ all periodicStrip ↔ raw.IsValid periodicStrip := by
  simp only [all, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨phase, phaseBelow, assignment, assignmentMem, equality⟩
    rw [TrominoAssignment.mem_words_iff] at assignmentMem
    subst raw
    exact ⟨phaseBelow, assignmentMem.1⟩
  · rintro ⟨phaseBelow, assignmentLength⟩
    refine ⟨raw.phase, phaseBelow, raw.assignment, ?_, rfl⟩
    rw [TrominoAssignment.mem_words_iff]
    exact ⟨assignmentLength, fun state _ =>
      TrominoAssignment.mem_assignmentStateList state⟩

@[simp]
theorem encode_mem_all {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    encode state ∈ all periodicStrip := by
  rw [mem_all_iff]
  exact encode_isValid state

/-- Every semantic frontier state is represented in the raw enumeration. -/
theorem exists_mem_all_decode_eq {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    ∃ raw ∈ all periodicStrip, decode periodicStrip raw = some state :=
  ⟨encode state, encode_mem_all state, decode_encode state⟩

end RawWindowState
end PeriodicStrip
end LeanTrominoes
