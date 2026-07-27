import LeanTrominoes.PeriodicOrthocrossingCarrierBoundingBox

/-!
# Source-segment support of retained carrier corridors

Every carrier node lies on one translated source segment.  Its physical
carrier axis is the source line scaled by twenty and shifted by the fixed
port coordinate six.  Consequently parallel carriers on distinct source
lines have widely separated narrow lens rectangles.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The translated source-drawing segment supporting a carrier node. -/
def CarrierNode.supportingSegment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) : GridSegment :=
  node.indexed.segment.translate
    ((drawing graph).periodTranslation node.translate)

/-- The fixed normal coordinate of a physical carrier is the corresponding
translated source line, scaled by twenty and shifted by six. -/
theorem carrierNode_position_normalCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph) :
    if node.isHorizontal then
      (node.position graph).2 =
        planarMacroScale * (node.supportingSegment graph).start.2 + 6
    else
      (node.position graph).1 =
        planarMacroScale * (node.supportingSegment graph).start.1 + 6 := by
  have aligned :
      node.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      node.indexed (carrierNode_indexed_mem graph nodeMem)
  have contains :=
    carrierNode_drawingPoint_contains graph nodeMem aligned
  have localData :=
    carrierNode_localPosition_axis_data graph nodeMem aligned
  by_cases horizontalTag : node.isHorizontal = true
  · rw [if_pos horizontalTag] at localData ⊢
    have horizontal :
        node.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
        graph nodeMem aligned).mp horizontalTag
    have supportingHorizontal :
        (node.supportingSegment graph).IsHorizontal := by
      exact
        (GridSegment.isHorizontal_translate _ _).mpr horizontal
    have drawingY :
        (node.drawingPoint graph).2 =
          (node.supportingSegment graph).start.2 := by
      rcases contains with onHorizontal | onVertical
      · exact onHorizontal.2.1
      · exact False.elim
          (onVertical.1.2 supportingHorizontal.1)
    rw [CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega
  · rw [if_neg horizontalTag] at localData ⊢
    have notHorizontal :
        ¬node.indexed.segment.IsHorizontal := by
      intro horizontal
      exact horizontalTag
        ((carrierNode_isHorizontal_iff
          graph nodeMem aligned).mpr horizontal)
    have vertical :
        node.indexed.segment.IsVertical :=
      aligned.resolve_left notHorizontal
    have supportingVertical :
        (node.supportingSegment graph).IsVertical := by
      exact
        (GridSegment.isVertical_translate _ _).mpr vertical
    have drawingX :
        (node.drawingPoint graph).1 =
          (node.supportingSegment graph).start.1 := by
      rcases contains with onHorizontal | onVertical
      · exact False.elim
          (supportingVertical.2 onHorizontal.1.1)
      · exact onVertical.2.1
    rw [CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega

/-- Horizontal retained links on different translated source rows have
strictly separated physical lens rectangles. -/
theorem
    drawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_normal_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ drawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ drawingCompleteCarrierLinks graph)
    (firstHorizontal :
      firstLink.first.isHorizontal = true)
    (secondHorizontal :
      secondLink.first.isHorizontal = true)
    (normalDifferent :
      (firstLink.first.supportingSegment graph).start.2 ≠
        (secondLink.first.supportingSegment graph).start.2) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1
  have secondNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  rw [if_pos firstHorizontal] at firstNormal
  rw [if_pos secondHorizontal] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [firstHorizontal, if_pos,
    secondHorizontal]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Vertical retained links on different translated source columns have
strictly separated physical lens rectangles. -/
theorem
    drawingCompleteCarrierLink_rectanglesSeparated_of_vertical_normal_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ drawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ drawingCompleteCarrierLinks graph)
    (firstVertical :
      ¬firstLink.first.isHorizontal = true)
    (secondVertical :
      ¬secondLink.first.isHorizontal = true)
    (normalDifferent :
      (firstLink.first.supportingSegment graph).start.1 ≠
        (secondLink.first.supportingSegment graph).start.1) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1
  have secondNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  rw [if_neg firstVertical] at firstNormal
  rw [if_neg secondVertical] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp [firstVertical, secondVertical]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

end PeriodicOrthocrossing
end LeanTrominoes
