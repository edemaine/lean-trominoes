import LeanTrominoes.StripFrontierIndexedSearch

/-!
# Packed arithmetic strip frontiers

The raw frontier representation stores a decoded assignment list.  The
space-bounded evaluator instead retains one base-nine natural and decodes
symbols on demand.  This file gives that packed representation a semantic
interface and proves that every packed transition is exactly the existing
raw transition after list decoding.

Repeated motif cells are handled by the same `List.idxOf` first-occurrence
rule as `RawWindowState.assignmentAtCell`; they are not assumed distinct.
-/

namespace LeanTrominoes
namespace PeriodicStrip

/-- Fixed-width arithmetic representation of one frontier state. -/
structure PackedWindowState where
  phase : Nat
  assignmentWord : Nat
  deriving DecidableEq, Repr

namespace PackedWindowState

open RawWindowState

/-- Decode a packed state to the established uniform raw representation. -/
def toRaw (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : RawWindowState where
  phase := packed.phase
  assignment :=
    decodeAssignmentStream
      (assignmentKeys periodicStrip).length
      packed.assignmentWord

/-- Packed state represented by one arithmetic search index. -/
def ofIndex (periodicStrip : PeriodicStrip)
    (stateIndex : Nat) : PackedWindowState where
  phase := stateIndex % periodicStrip.period
  assignmentWord := stateIndex / periodicStrip.period

@[simp]
theorem toRaw_ofIndex (periodicStrip : PeriodicStrip)
    (stateIndex : Nat) :
    (ofIndex periodicStrip stateIndex).toRaw periodicStrip =
      RawWindowState.ofIndex periodicStrip stateIndex := by
  simp [toRaw, ofIndex, RawWindowState.ofIndex,
    decodeAssignmentStream_eq_decodeAssignment]

/-- Position selected by the raw encoding's first-occurrence lookup. -/
def assignmentPosition (periodicStrip : PeriodicStrip)
    (column : WindowColumn) (cell : Cell) : Nat :=
  @List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
    (column, cell) (assignmentKeys periodicStrip)

/-- Read a packed assignment symbol arithmetically. -/
def assignmentAtCell (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (cell : Cell) : Option SquareSymmetry :=
  let position :=
    assignmentPosition periodicStrip column cell
  if position < (assignmentKeys periodicStrip).length then
    assignmentOfDigit
      (assignmentDigitAt packed.assignmentWord position)
  else
    none

@[simp]
theorem assignmentAtCell_toRaw
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (cell : Cell) :
    packed.assignmentAtCell periodicStrip column cell =
      (packed.toRaw periodicStrip).assignmentAtCell
        periodicStrip column cell := by
  unfold assignmentAtCell assignmentPosition
    RawWindowState.assignmentAtCell toRaw
  rw [decodeAssignmentStream_eq_decodeAssignment,
    getD_decodeAssignment]

/-- Horizontal phase represented by one packed window column. -/
def columnPhase (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  (packed.phase + column.val + 2 * periodicStrip.period - 2) %
    periodicStrip.period

@[simp]
theorem columnPhase_toRaw
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packed.columnPhase periodicStrip column =
      (packed.toRaw periodicStrip).columnPhase
        periodicStrip column := by
  rfl

/-- Packed assignment value at one row of a window column. -/
def valueAt (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (row : Int) : Option SquareSymmetry :=
  packed.assignmentAtCell periodicStrip column
    ((packed.columnPhase periodicStrip column : Int), row)

@[simp]
theorem valueAt_toRaw
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (row : Int) :
    packed.valueAt periodicStrip column row =
      (packed.toRaw periodicStrip).valueAt
        periodicStrip column row := by
  simp [valueAt, RawWindowState.valueAt]

/-- Packed assignment on coordinates relative to the window center. -/
def localAssignment (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : TrominoAssignment :=
  fun offset =>
    match WindowColumn.ofDisplacementCode? offset.1 with
    | some column => packed.valueAt periodicStrip column offset.2
    | none => none

@[simp]
theorem localAssignment_toRaw
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packed.localAssignment periodicStrip =
      (packed.toRaw periodicStrip).localAssignment
        periodicStrip := by
  funext offset
  unfold localAssignment RawWindowState.localAssignment
  cases selected :
      WindowColumn.ofDisplacementCode? offset.1 with
  | none => rfl
  | some column =>
      exact valueAt_toRaw periodicStrip packed column offset.2

/-- Candidate placements selected by a packed local assignment. -/
def activePlacementList (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (row : Int) :
    List (Placement Unit) :=
  (TrominoAssignment.coveringPlacementList tromino (0, row)).filter
    fun placement =>
      packed.localAssignment periodicStrip placement.offset =
        some placement.symmetry

@[simp]
theorem activePlacementList_toRaw
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (row : Int) :
    packed.activePlacementList tromino periodicStrip row =
      (packed.toRaw periodicStrip).activePlacementList
        tromino periodicStrip row := by
  simp [activePlacementList,
    RawWindowState.activePlacementList]

/-- Packed normalization check at one motif occurrence. -/
def normalizedAtBool (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (base : Cell) : Bool :=
  decide
      (base.1 =
        (packed.columnPhase periodicStrip column : Int)) ||
    decide
      (packed.assignmentAtCell periodicStrip column base = none)

def normalizedColumnBool (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Bool :=
  periodicStrip.motif.all fun base =>
    packed.normalizedAtBool periodicStrip column base

def isNormalizedBool (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Bool :=
  (List.finRange 5).all fun column =>
    packed.normalizedColumnBool periodicStrip column

@[simp]
theorem isNormalizedBool_toRaw
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packed.isNormalizedBool periodicStrip =
      (packed.toRaw periodicStrip).isNormalizedBool
        periodicStrip := by
  simp [isNormalizedBool, normalizedColumnBool,
    normalizedAtBool, RawWindowState.isNormalizedBool,
    RawWindowState.normalizedColumnBool,
    RawWindowState.normalizedAtBool, motifCells]

/-- Packed containment check for one possible source cell. -/
def centerSourceInsideBool (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (symmetry : SquareSymmetry) (source : Cell) : Bool :=
  periodicStrip.contains
    (Cell.add ((packed.phase : Int), base.2)
      (symmetry.act source))

def centerSymmetryInsideBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (symmetry : SquareSymmetry) : Bool :=
  decide
      (packed.assignmentAtCell periodicStrip
          WindowState.center base ≠ some symmetry) ||
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip
        base symmetry source

def centerBaseInsideBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Bool :=
  decide (base.1 ≠ (packed.phase : Int)) ||
    TrominoAssignment.squareSymmetryList.all fun symmetry =>
      packed.centerSymmetryInsideBool
        tromino periodicStrip base symmetry

def centerInsideBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Bool :=
  periodicStrip.motif.all fun base =>
    packed.centerBaseInsideBool tromino periodicStrip base

def centerBaseCoveredBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Bool :=
  decide (base.1 ≠ (packed.phase : Int)) ||
    decide
      ((packed.activePlacementList
        tromino periodicStrip base.2).length = 1)

def centerCoveredBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Bool :=
  periodicStrip.motif.all fun base =>
    packed.centerBaseCoveredBool tromino periodicStrip base

def isCenterValidBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Bool :=
  packed.centerInsideBool tromino periodicStrip &&
    packed.centerCoveredBool tromino periodicStrip

@[simp]
theorem isCenterValidBool_toRaw
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packed.isCenterValidBool tromino periodicStrip =
      (packed.toRaw periodicStrip).isCenterValidBool
        tromino periodicStrip := by
  simp [isCenterValidBool, centerInsideBool,
    centerBaseInsideBool, centerSymmetryInsideBool,
    centerSourceInsideBool, centerCoveredBool,
    centerBaseCoveredBool,
    RawWindowState.isCenterValidBool,
    RawWindowState.centerInsideBool,
    RawWindowState.centerBaseInsideBool,
    RawWindowState.centerSymmetryInsideBool,
    RawWindowState.centerSourceInsideBool,
    RawWindowState.centerCoveredBool,
    RawWindowState.centerBaseCoveredBool, motifCells, toRaw]

/-- Packed shared-assignment check at one overlap motif occurrence. -/
def overlapsAtBool (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (base : Cell) : Bool :=
  decide
    (current.assignmentAtCell periodicStrip column.succ base =
      next.assignmentAtCell periodicStrip column.castSucc base)

def overlapsColumnBool (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Bool :=
  periodicStrip.motif.all fun base =>
    current.overlapsAtBool periodicStrip next column base

def overlapsBool (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Bool :=
  decide
      (next.phase =
        (current.phase + 1) % periodicStrip.period) &&
    (List.finRange 4).all fun column =>
      current.overlapsColumnBool periodicStrip next column

@[simp]
theorem overlapsBool_toRaw
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    current.overlapsBool periodicStrip next =
      (current.toRaw periodicStrip).overlapsBool
        periodicStrip (next.toRaw periodicStrip) := by
  simp [overlapsBool, overlapsColumnBool, overlapsAtBool,
    RawWindowState.overlapsBool,
    RawWindowState.overlapsColumnBool,
    RawWindowState.overlapsAtBool, motifCells, toRaw]

/-- Complete packed raw-transition predicate. -/
def transitionBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Bool :=
  current.isNormalizedBool periodicStrip &&
    current.isCenterValidBool tromino periodicStrip &&
      current.overlapsBool periodicStrip next

@[simp]
theorem transitionBool_toRaw
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    current.transitionBool tromino periodicStrip next =
      (current.toRaw periodicStrip).transitionBool
        tromino periodicStrip (next.toRaw periodicStrip) := by
  simp [transitionBool, RawWindowState.transitionBool]

theorem indexedTransitionRawBool_eq_packed
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    RawWindowState.indexedTransitionRawBool
        tromino periodicStrip first last =
      (ofIndex periodicStrip first).transitionBool
        tromino periodicStrip (ofIndex periodicStrip last) := by
  simp [RawWindowState.indexedTransitionRawBool]

end PackedWindowState
end PeriodicStrip
end LeanTrominoes
