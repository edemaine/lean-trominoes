import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-!
# Core period translations for physical carrier data

This file defines the common drawing-period action on crossings, boundaries,
terminals, carrier nodes, and positioned equality links.  It is intentionally
upstream of retained-link enumeration so finite crossing windows can be
defined as bounded orbits of canonical crossings.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translate a physical crossing record by a number of drawing periods. -/
def CrossingRecord.periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) : CrossingRecord where
  first := record.first
  firstTranslate := Cell.add record.firstTranslate shift
  second := record.second
  secondTranslate := Cell.add record.secondTranslate shift
  point := Cell.add record.point
    ((drawing graph).periodTranslation shift)

/-- Translate a crossing boundary while preserving its port side. -/
def CrossingBoundary.periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    CrossingBoundary :=
  ⟨boundary.crossing.periodTranslate graph shift, boundary.side⟩

/-- Translate one segment terminal to another occurrence of the same indexed
segment. -/
def SegmentTerminal.periodTranslate
    (terminal : SegmentTerminal) (shift : Cell) :
    SegmentTerminal :=
  ⟨terminal.indexed, Cell.add terminal.translate shift,
    terminal.endpoint⟩

/-- Translate either kind of physical carrier node. -/
def CarrierNode.periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) : CarrierNode :=
  match node with
  | CarrierNode.boundary crossingBoundary =>
      CarrierNode.boundary
        (crossingBoundary.periodTranslate graph shift)
  | CarrierNode.terminal segmentTerminal =>
      CarrierNode.terminal
        (segmentTerminal.periodTranslate shift)

/-- The refined macro-grid translation corresponding to a drawing-period
shift. -/
def carrierMacroPeriodTranslation
    {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (shift : Cell) : Cell :=
  Cell.scale
    (planarMacroScale * drawingGridSize graph) shift

/-- Translate both clause positions of an equality link. -/
def EqualityPositions.periodTranslate
    (positions : EqualityPositions) (offset : Cell) :
    EqualityPositions :=
  ⟨Cell.add positions.forward offset,
    Cell.add positions.backward offset⟩

/-- Translate a physical carrier link, including its two geometric clause
positions. -/
def carrierLinkPeriodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    EqualityLink CarrierNode where
  first := link.first.periodTranslate graph shift
  second := link.second.periodTranslate graph shift
  positions := EqualityPositions.periodTranslate link.positions
    (carrierMacroPeriodTranslation graph shift)

@[simp]
theorem carrierLinkPeriodTranslate_first
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    (carrierLinkPeriodTranslate graph link shift).first =
      link.first.periodTranslate graph shift := rfl

@[simp]
theorem carrierLinkPeriodTranslate_second
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    (carrierLinkPeriodTranslate graph link shift).second =
      link.second.periodTranslate graph shift := rfl

/-- Translating a crossing adds the common lattice shift to its extracted
period quotient. -/
theorem crossingPeriodShift_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    crossingPeriodShift graph
        (record.periodTranslate graph shift) =
      Cell.add (crossingPeriodShift graph record) shift := by
  have sizeNe : (drawingGridSize graph : Int) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (drawingGridSize_pos graph)
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate,
      ⟨pointX, pointY⟩⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [CrossingRecord.periodTranslate,
      crossingPeriodShift,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale,
      Int.add_mul_ediv_left _ _ sizeNe]

/-- Periodic normalization forgets a common physical translation. -/
theorem CrossingRecord.periodNormalize_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).periodNormalize graph =
      record.periodNormalize graph := by
  unfold CrossingRecord.periodNormalize
  rw [crossingPeriodShift_periodTranslate]
  rcases record with
    ⟨first, ⟨firstX, firstY⟩,
      second, ⟨secondX, secondY⟩,
      ⟨pointX, pointY⟩⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    PeriodicGridDrawing.normalizePoint,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- Boundary normalization is likewise invariant under common physical
translation. -/
@[simp]
theorem CrossingBoundary.periodNormalize_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    (boundary.periodTranslate graph shift).periodNormalize graph =
      boundary.periodNormalize graph := by
  rcases boundary with ⟨crossing, side⟩
  simp [CrossingBoundary.periodTranslate,
    CrossingBoundary.periodNormalize,
    CrossingRecord.periodNormalize_periodTranslate]

/-- Zero acts trivially on crossing records. -/
@[simp]
theorem CrossingRecord.periodTranslate_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) :
    record.periodTranslate graph (0, 0) = record := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  simp [CrossingRecord.periodTranslate,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]

/-- Zero acts trivially on crossing boundaries. -/
@[simp]
theorem CrossingBoundary.periodTranslate_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) :
    boundary.periodTranslate graph (0, 0) = boundary := by
  rcases boundary with ⟨crossing, side⟩
  simp [CrossingBoundary.periodTranslate]

end PeriodicOrthocrossing
end LeanTrominoes
