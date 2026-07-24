import LeanTrominoes.ComputableSearch
import LeanTrominoes.StripFrontier

/-!
# Uniform encodings of sparse strip frontiers

`WindowState periodicStrip` is the convenient semantic representation of a
strip frontier, but its type depends on the input strip and its assignment is
a function.  This file gives the same data a uniform, list-based
representation.  The five window columns are ordered first, and within each
column the cells follow the input motif order.  Repeated motif cells therefore
create redundant raw coordinates; `assignmentAtCell` consistently reads the
first copy.

The raw representation is what a space-bounded evaluator can store and
generate on demand.  In particular, its assignment word has exactly
`5 * periodicStrip.motif.length` symbols over the existing nine-symbol
assignment alphabet.  Avoiding a deduplication pass is useful to the
space-bounded evaluator, while the semantic projection still collapses
repeated cells to one motif-cell assignment.
-/

namespace LeanTrominoes
namespace PeriodicStrip

/-- A strip-frontier state represented without an input-dependent type. -/
structure RawWindowState where
  phase : Nat
  assignment : List (Option SquareSymmetry)
  deriving DecidableEq, Repr

namespace RawWindowState

/-- Product representation used by the standard computability encoding. -/
def equivData :
    RawWindowState ≃ Nat × List (Option SquareSymmetry) where
  toFun raw := (raw.phase, raw.assignment)
  invFun data := ⟨data.1, data.2⟩
  left_inv raw := by cases raw; rfl
  right_inv data := by cases data; rfl

noncomputable instance : Primcodable RawWindowState :=
  Primcodable.ofEquiv (Nat × List (Option SquareSymmetry)) equivData

/-- The motif traversal used by the raw encoding. -/
def motifCells (periodicStrip : PeriodicStrip) : List Cell :=
  periodicStrip.motif

@[simp]
theorem length_motifCells (periodicStrip : PeriodicStrip) :
    (motifCells periodicStrip).length =
      periodicStrip.motif.length := by
  rfl

@[simp]
theorem mem_motifCells (periodicStrip : PeriodicStrip) (cell : Cell) :
    cell ∈ motifCells periodicStrip ↔
      cell ∈ periodicStrip.motif.toFinset := by
  simp [motifCells]

/-- Canonical order of the five copies of the input motif traversal. -/
def assignmentKeys (periodicStrip : PeriodicStrip) :
    List (WindowColumn × Cell) :=
  (List.finRange 5).flatMap fun column =>
    (motifCells periodicStrip).map fun cell => (column, cell)

@[simp]
theorem length_assignmentKeys (periodicStrip : PeriodicStrip) :
    (assignmentKeys periodicStrip).length =
      5 * periodicStrip.motif.length := by
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

/-- Read an assignment value at an untyped motif cell from a raw word. -/
def assignmentAtCell (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (column : WindowColumn) (cell : Cell) :
    Option SquareSymmetry :=
  raw.assignment.getD
    (@List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
      (column, cell) (assignmentKeys periodicStrip)) none

/-- Read one semantic assignment value from a raw assignment word. -/
def assignmentAt (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (column : WindowColumn) (base : periodicStrip.MotifCell) :
    Option SquareSymmetry :=
  raw.assignmentAtCell periodicStrip column base.val

/-- Interpret a valid raw state as a dependent semantic frontier state. -/
def toWindowState (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (valid : raw.IsValid periodicStrip) :
    WindowState periodicStrip where
  phase := ⟨raw.phase, valid.1⟩
  assignment := raw.assignmentAt periodicStrip

/-- Decode a well-sized raw state into the dependent semantic state type. -/
def decode (periodicStrip : PeriodicStrip) (raw : RawWindowState) :
    Option (WindowState periodicStrip) :=
  if valid : raw.IsValid periodicStrip then
    some (raw.toWindowState periodicStrip valid)
  else
    none

theorem decode_eq_some_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip) :
    decode periodicStrip raw =
      some (raw.toWindowState periodicStrip valid) := by
  rw [decode, dif_pos valid]

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

private theorem getD_map_idxOf_of_mem {α β : Type*} [DecidableEq α]
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
        (@List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
          (column, base.val) (assignmentKeys periodicStrip)) none =
      state.assignment column base
  calc
    _ = semanticAssignmentAtCell state (column, base.val) :=
      getD_map_idxOf_of_mem _ _ _
        (mem_assignmentKeys periodicStrip column base)
    _ = state.assignment column base :=
      semanticAssignmentAtCell_base state column base

@[simp]
theorem toWindowState_encode {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    (encode state).toWindowState periodicStrip (encode_isValid state) =
      state := by
  cases state with
  | mk phase assignment =>
      unfold toWindowState
      congr 1
      funext column base
      exact assignmentAt_encode ⟨phase, assignment⟩ column base

@[simp]
theorem decode_encode {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    decode periodicStrip (encode state) = some state := by
  rw [decode, dif_pos (encode_isValid state)]
  exact congrArg some (toWindowState_encode state)

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
