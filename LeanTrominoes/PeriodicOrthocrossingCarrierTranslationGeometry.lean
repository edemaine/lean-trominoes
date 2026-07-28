import LeanTrominoes.PeriodicOrthocrossingCarrierRepresentativeTranslation

/-!
# Geometric covariance of carrier translation

Common drawing-period translation moves every refined carrier position by the
same macro-period vector.  Consequently it preserves carrier orientation,
the order test used to place equality clauses, crossover-site identity, and
the conversion from adjacent carrier nodes to positioned equality links.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translating a crossing boundary moves its refined position by the
corresponding macro-period vector. -/
@[simp]
theorem CrossingBoundary.position_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    (boundary.periodTranslate graph shift).position =
      Cell.add boundary.position
        (carrierMacroPeriodTranslation graph shift) := by
  rcases boundary with ⟨crossing, side⟩
  rcases crossing with
    ⟨first, firstTranslate, second, secondTranslate,
      ⟨pointX, pointY⟩⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [CrossingBoundary.periodTranslate,
      CrossingRecord.periodTranslate,
      CrossingBoundary.position, crossingMacroOrigin,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale] <;>
    ring

/-- Translating a terminal moves its refined position by the corresponding
macro-period vector. -/
@[simp]
theorem SegmentTerminal.position_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal) (shift : Cell) :
    (terminal.periodTranslate shift).position graph =
      Cell.add (terminal.position graph)
        (carrierMacroPeriodTranslation graph shift) := by
  rcases terminal with ⟨indexed, translate, endpoint⟩
  change
    SegmentTerminal.position graph
        ⟨indexed, Cell.add translate shift, endpoint⟩ =
      Cell.add
        (SegmentTerminal.position graph
          ⟨indexed, translate, endpoint⟩)
        (carrierMacroPeriodTranslation graph shift)
  rw [SegmentTerminal.position_translate graph indexed endpoint
      (Cell.add translate shift),
    SegmentTerminal.position_translate graph indexed endpoint translate]
  rcases translate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [SegmentTerminal.periodTranslate,
      carrierMacroPeriodTranslation, Cell.add, Cell.scale] <;>
    ring

/-- Every kind of carrier node moves by the same refined period vector. -/
@[simp]
theorem CarrierNode.position_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).position graph =
      Cell.add (node.position graph)
        (carrierMacroPeriodTranslation graph shift) := by
  cases node with
  | boundary boundary =>
      simpa [CarrierNode.periodTranslate, CarrierNode.position] using
        CrossingBoundary.position_periodTranslate graph boundary shift
  | terminal terminal =>
      simpa [CarrierNode.periodTranslate, CarrierNode.position] using
        SegmentTerminal.position_periodTranslate graph terminal shift

/-- Period translation does not change the carrier's axis. -/
@[simp]
theorem CarrierNode.isHorizontal_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).isHorizontal =
      node.isHorizontal := by
  cases node with
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      cases side <;>
        rfl
  | terminal terminal =>
      rfl

/-- Period translation adds the appropriate component of the macro-period
vector to the carrier order coordinate. -/
theorem CarrierNode.orderCoordinate_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).orderCoordinate graph =
      if node.isHorizontal then
        node.orderCoordinate graph +
          (carrierMacroPeriodTranslation graph shift).1
      else
        node.orderCoordinate graph +
          (carrierMacroPeriodTranslation graph shift).2 := by
  rw [CarrierNode.orderCoordinate,
    CarrierNode.isHorizontal_periodTranslate,
    CarrierNode.position_periodTranslate]
  by_cases horizontal : node.isHorizontal
  · simp [horizontal, CarrierNode.orderCoordinate, Cell.add]
  · simp [horizontal, CarrierNode.orderCoordinate, Cell.add]

/-- A common translation preserves the relative order-coordinate comparison
of two nodes. -/
theorem CarrierNode.orderCoordinate_periodTranslate_le_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) (shift : Cell)
    (sameAxis : first.isHorizontal = second.isHorizontal) :
    (first.periodTranslate graph shift).orderCoordinate graph ≤
        (second.periodTranslate graph shift).orderCoordinate graph ↔
      first.orderCoordinate graph ≤ second.orderCoordinate graph := by
  rw [CarrierNode.orderCoordinate_periodTranslate,
    CarrierNode.orderCoordinate_periodTranslate]
  rw [sameAxis]
  split <;> omega

/-- Common period translation preserves the two positioned equality clauses
generated from an ordered carrier-node pair. -/
@[simp]
theorem carrierNodeEqualityPositions_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) (shift : Cell) :
    carrierNodeEqualityPositions graph
        (first.periodTranslate graph shift)
        (second.periodTranslate graph shift) =
      EqualityPositions.periodTranslate
        (carrierNodeEqualityPositions graph first second)
        (carrierMacroPeriodTranslation graph shift) := by
  rcases firstPositionEq : first.position graph with
    ⟨firstX, firstY⟩
  rcases secondPositionEq : second.position graph with
    ⟨secondX, secondY⟩
  rcases shiftEq : carrierMacroPeriodTranslation graph shift with
    ⟨shiftX, shiftY⟩
  by_cases horizontal : first.isHorizontal
  · simp [carrierNodeEqualityPositions, horizontal,
      EqualityPositions.periodTranslate, Cell.add,
      firstPositionEq, secondPositionEq, shiftEq] <;>
      split_ifs <;> constructor <;> ring
  · simp [carrierNodeEqualityPositions, horizontal,
      EqualityPositions.periodTranslate, Cell.add,
      firstPositionEq, secondPositionEq, shiftEq] <;>
      split_ifs <;> constructor <;> ring

/-- Translating a pair before constructing its link agrees with translating
the constructed positioned equality link. -/
@[simp]
theorem carrierNodePairLink_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : CarrierNode × CarrierNode) (shift : Cell) :
    carrierNodePairLink graph
        (pair.1.periodTranslate graph shift,
          pair.2.periodTranslate graph shift) =
      carrierLinkPeriodTranslate graph
        (carrierNodePairLink graph pair) shift := by
  rcases pair with ⟨first, second⟩
  simp [carrierNodePairLink, carrierLinkPeriodTranslate]

/-- Translating back by the inverse shift recovers the original crossing
record. -/
@[simp]
theorem CrossingRecord.periodTranslate_neg
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).periodTranslate graph
        (Cell.neg shift) =
      record := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    PeriodicGridDrawing.periodTranslation,
    Cell.neg, Cell.sub, Cell.add, Cell.scale]

/-- Common period translation is injective on physical crossing records. -/
theorem CrossingRecord.periodTranslate_injective
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (shift : Cell) :
    Function.Injective fun record : CrossingRecord =>
      record.periodTranslate graph shift := by
  intro first second equal
  have translatedBack :=
    congrArg
      (fun record : CrossingRecord =>
        record.periodTranslate graph (Cell.neg shift))
      equal
  simpa using translatedBack

/-- Common period translation preserves whether two carrier ports belong to
the same crossover site. -/
@[simp]
theorem CarrierNode.sameCrossoverSite_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) (shift : Cell) :
    (first.periodTranslate graph shift).sameCrossoverSite
        (second.periodTranslate graph shift) =
      first.sameCrossoverSite second := by
  cases first with
  | terminal firstTerminal =>
      cases second <;>
        rfl
  | boundary firstBoundary =>
      cases second with
      | terminal secondTerminal =>
          rfl
      | boundary secondBoundary =>
          by_cases same :
              firstBoundary.crossing = secondBoundary.crossing
          · simp [CarrierNode.periodTranslate,
              CarrierNode.sameCrossoverSite,
              CrossingBoundary.periodTranslate, same]
          · have translatedDifferent :
                firstBoundary.crossing.periodTranslate graph shift ≠
                  secondBoundary.crossing.periodTranslate graph shift :=
              fun equal =>
                same
                  (CrossingRecord.periodTranslate_injective
                    graph shift equal)
            simp [CarrierNode.periodTranslate,
              CarrierNode.sameCrossoverSite,
              CrossingBoundary.periodTranslate,
              same, translatedDifferent]

end PeriodicOrthocrossing
end LeanTrominoes
