import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierSupportGeometry
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation

/-!
# Geometry of translated selected retained carriers

A selected retained carrier link can be viewed in any drawing-period
translate, even when that translated occurrence lies outside the finite
retention window.  Its supporting source segment and explicit lens rectangle
translate covariantly.  These identities let the retained corridor bounds be
used directly in the infinite periodic drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translating a carrier node translates its physical supporting source
segment by the corresponding drawing-period vector. -/
@[simp]
theorem CarrierNode.supportingSegment_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).supportingSegment graph =
      (node.supportingSegment graph).translate
        ((drawing graph).periodTranslation shift) := by
  unfold CarrierNode.supportingSegment
  rw [CarrierNode.indexed_periodTranslate,
    CarrierNode.translate_periodTranslate]
  rcases translateEq : node.translate with
    ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  rcases segmentEq : node.indexed.segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [
    PeriodicGridDrawing.periodTranslation,
    GridSegment.translate, Cell.add, Cell.scale]
  congr 1 <;> apply Prod.ext <;> simp <;> ring

/-- The lower corner of a translated selected carrier lens is the translate
of its original lower corner. -/
@[simp]
theorem drawingCompleteCarrierLinkRectangleLower_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph link shift) =
      Cell.add
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (carrierMacroPeriodTranslation graph shift) := by
  unfold drawingCompleteCarrierLinkRectangleLower
  simp only [carrierLinkPeriodTranslate_first,
    CarrierNode.isHorizontal_periodTranslate,
    CarrierNode.position_periodTranslate]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [horizontal, Cell.add]
    ring
  · simp [horizontal, Cell.add]
    ring

/-- The upper corner of a translated selected carrier lens is the translate
of its original upper corner. -/
@[simp]
theorem drawingCompleteCarrierLinkRectangleUpper_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph link shift) =
      Cell.add
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (carrierMacroPeriodTranslation graph shift) := by
  unfold drawingCompleteCarrierLinkRectangleUpper
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.isHorizontal_periodTranslate,
    CarrierNode.position_periodTranslate]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [horizontal, Cell.add]
    ring
  · simp [horizontal, Cell.add]
    ring

/-- A period translate of a selected horizontal retained link stays within
the corresponding translated source corridor. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_horizontal_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontal : link.first.isHorizontal = true)
    (shift : Cell) :
    planarMacroScale *
          min
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).start.1
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).finish.1 +
        11 ≤
      ((carrierLinkPeriodTranslate graph link shift).first
        |>.position graph).1 ∧
    ((carrierLinkPeriodTranslate graph link shift).second
        |>.position graph).1 ≤
      planarMacroScale *
          max
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).start.1
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).finish.1 +
        1 := by
  have base :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal linkMem horizontal
  simp only [planarMacroScale] at base
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.supportingSegment_periodTranslate,
    CarrierNode.position_periodTranslate]
  simp only [GridSegment.translate, Cell.add,
    PeriodicGridDrawing.periodTranslation,
    carrierMacroPeriodTranslation, Cell.scale,
    min_add_add_left, max_add_add_left,
    planarMacroScale, drawing_gridSize]
  constructor <;> nlinarith [base.1, base.2]

/-- A period translate of a selected vertical retained link stays within the
corresponding translated source corridor. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_vertical_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (vertical : ¬link.first.isHorizontal = true)
    (shift : Cell) :
    planarMacroScale *
          min
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).start.2
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).finish.2 +
        11 ≤
      ((carrierLinkPeriodTranslate graph link shift).first
        |>.position graph).2 ∧
    ((carrierLinkPeriodTranslate graph link shift).second
        |>.position graph).2 ≤
      planarMacroScale *
          max
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).start.2
            ((carrierLinkPeriodTranslate graph link shift).first
              |>.supportingSegment graph).finish.2 +
        1 := by
  have base :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal linkMem vertical
  simp only [planarMacroScale] at base
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.supportingSegment_periodTranslate,
    CarrierNode.position_periodTranslate]
  simp only [GridSegment.translate, Cell.add,
    PeriodicGridDrawing.periodTranslation,
    carrierMacroPeriodTranslation, Cell.scale,
    min_add_add_left, max_add_add_left,
    planarMacroScale, drawing_gridSize]
  constructor <;> nlinarith [base.1, base.2]

/-- The physical normal-coordinate formula for a selected retained node is
preserved by arbitrary period translation. -/
theorem retainedCarrierNode_periodTranslate_position_normalCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (shift : Cell) :
    if (node.periodTranslate graph shift).isHorizontal then
      ((node.periodTranslate graph shift).position graph).2 =
        planarMacroScale *
            ((node.periodTranslate graph shift).supportingSegment graph
              ).start.2 +
          6
    else
      ((node.periodTranslate graph shift).position graph).1 =
        planarMacroScale *
            ((node.periodTranslate graph shift).supportingSegment graph
              ).start.1 +
          6 := by
  have base :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal nodeMem
  simp only [planarMacroScale] at base
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [CarrierNode.isHorizontal_periodTranslate,
    CarrierNode.position_periodTranslate,
    CarrierNode.supportingSegment_periodTranslate]
  by_cases horizontal : node.isHorizontal = true
  · rw [if_pos horizontal] at base ⊢
    simp only [GridSegment.translate, Cell.add,
      PeriodicGridDrawing.periodTranslation,
      carrierMacroPeriodTranslation, Cell.scale,
      planarMacroScale, drawing_gridSize]
    nlinarith
  · rw [if_neg horizontal] at base ⊢
    simp only [GridSegment.translate, Cell.add,
      PeriodicGridDrawing.periodTranslation,
      carrierMacroPeriodTranslation, Cell.scale,
      planarMacroScale, drawing_gridSize]
    nlinarith

end PeriodicOrthocrossing
end LeanTrominoes
