import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree

/-!
# Translating retained carrier data

Periodic ownership is useful only if a physical link can be moved to its
zero-shift representative without changing the normalized periodic link.
This file supplies that algebra.  Crossing records, boundaries, terminals,
carrier nodes, equality positions, and equality links all receive a common
lattice translation.  Crossing normalization is invariant, normalization
offsets add the common shift, and `PeriodicEquality.normalizeLink` cancels it.
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

/-- Translate the occurrence coordinate of a physical carrier key. -/
def periodTranslateCarrierKey
    (key : Nat × Nat × Cell) (shift : Cell) :
    Nat × Nat × Cell :=
  (key.1, key.2.1, Cell.add key.2.2 shift)

/-- Translating a carrier node translates exactly its occurrence key. -/
@[simp]
theorem CarrierNode.carrierKey_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).carrierKey =
      periodTranslateCarrierKey node.carrierKey shift := by
  cases node with
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        periodTranslateCarrierKey,
        CarrierNode.carrierKey,
        SegmentTerminal.carrierKey,
        PeriodicGridDrawing.SegmentOccurrenceKey]
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      rcases crossing with
        ⟨first, firstTranslate, second, secondTranslate, point⟩
      cases side <;>
        simp [CarrierNode.periodTranslate,
          CrossingBoundary.periodTranslate,
          CrossingRecord.periodTranslate,
          periodTranslateCarrierKey,
          CarrierNode.carrierKey,
          CrossingBoundary.carrierKey,
          PeriodicGridDrawing.SegmentOccurrenceKey]

/-- Translating a carrier node preserves its periodic prototype and adds the
common shift to its normalization offset. -/
theorem normalizeCarrierNode_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    normalizeCarrierNode graph
        (node.periodTranslate graph shift) =
      ((normalizeCarrierNode graph node).1,
        Cell.add (normalizeCarrierNode graph node).2 shift) := by
  cases node with
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        normalizeCarrierNode]
  | boundary boundary =>
      change
        (PeriodicCarrierNode.boundary
            ((boundary.periodTranslate graph shift).periodNormalize graph),
          crossingPeriodShift graph
            (boundary.periodTranslate graph shift).crossing) =
        (PeriodicCarrierNode.boundary
            (boundary.periodNormalize graph),
          Cell.add
            (crossingPeriodShift graph boundary.crossing) shift)
      rw [CrossingBoundary.periodNormalize_periodTranslate]
      apply Prod.ext
      · rfl
      · simpa [CrossingBoundary.periodTranslate] using
          crossingPeriodShift_periodTranslate
            graph boundary.crossing shift

/-- A common physical translation cancels out of the normalized periodic
equality link. -/
@[simp]
theorem normalizeLink_carrierLinkPeriodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (carrierLinkPeriodTranslate graph link shift) =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        link := by
  rcases shift with ⟨shiftX, shiftY⟩
  rcases normalizeCarrierNode graph link.first with
    ⟨first, ⟨firstX, firstY⟩⟩
  rcases normalizeCarrierNode graph link.second with
    ⟨second, ⟨secondX, secondY⟩⟩
  simp [PeriodicEquality.normalizeLink,
    carrierLinkPeriodTranslate,
    normalizeCarrierNode_periodTranslate,
    Cell.add, Cell.sub]

end PeriodicOrthocrossing
end LeanTrominoes
