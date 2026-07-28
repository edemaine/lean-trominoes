import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierOrder

/-!
# Common-axis geometry for retained carrier nodes

Retained boundary nodes obey the same supporting-segment and local-port
geometry as canonical boundary nodes.  These facts supply the common physical
axis and the modulo-ten axial spacing used by every retained equality lens.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A retained carrier node's drawing point lies on its translated supporting
segment, with terminals allowed at the closed endpoints. -/
theorem retainedCarrierNode_drawingPoint_contains
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    (node.indexed.segment.translate
        ((drawing graph).periodTranslation node.translate)).Contains
      (node.drawingPoint graph) := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      simpa [CarrierNode.indexed, CarrierNode.translate,
        CarrierNode.drawingPoint] using
        GridSegment.contains_of_interiorContains
          (retainedCrossingBoundary_indexed_mem_and_contains
            graph boundaryMem).2
  | terminal terminal =>
      simp only [CarrierNode.indexed] at axisAligned
      have translatedAligned :
          (terminal.indexed.segment.translate
            ((drawing graph).periodTranslation
              terminal.translate)).IsAxisAligned :=
        (GridSegment.isAxisAligned_translate _ _).mpr axisAligned
      generalize endpointEqual : terminal.endpoint = endpoint
      cases endpoint with
      | start =>
          simpa [CarrierNode.indexed, CarrierNode.translate,
            CarrierNode.drawingPoint,
            SegmentTerminal.drawingPoint, endpointEqual] using
            GridSegment.contains_start_of_axisAligned translatedAligned
      | finish =>
          simpa [CarrierNode.indexed, CarrierNode.translate,
            CarrierNode.drawingPoint,
            SegmentTerminal.drawingPoint, endpointEqual] using
            GridSegment.contains_finish_of_axisAligned translatedAligned

/-- On a retained carrier, the node's Boolean axis tag agrees with its
supporting indexed segment. -/
theorem retainedCarrierNode_isHorizontal_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    node.isHorizontal = true ↔
      node.indexed.segment.IsHorizontal := by
  cases node with
  | terminal terminal =>
      simp [CarrierNode.isHorizontal, CarrierNode.indexed]
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      have crossingMem :=
        retainedCrossingBoundary_crossing_mem graph boundaryMem
      have axes :=
        retainedCrossing_firstHorizontal_secondVertical
          graph crossingMem
      cases boundary with
      | mk crossing side =>
          cases side
          · have horizontal :=
              (GridSegment.isHorizontal_translate _ _).mp axes.1
            constructor
            · intro
              simpa [CarrierNode.indexed,
                CrossingBoundary.indexed] using horizontal
            · intro
              rfl
          · have horizontal :=
              (GridSegment.isHorizontal_translate _ _).mp axes.1
            constructor
            · intro
              simpa [CarrierNode.indexed,
                CrossingBoundary.indexed] using horizontal
            · intro
              rfl
          · simp only [CarrierNode.isHorizontal, CarrierNode.indexed,
              CrossingBoundary.indexed, Bool.false_eq_true,
              false_iff]
            have vertical :=
              (GridSegment.isVertical_translate _ _).mp axes.2
            exact fun horizontal => vertical.2 horizontal.1
          · simp only [CarrierNode.isHorizontal, CarrierNode.indexed,
              CrossingBoundary.indexed, Bool.false_eq_true,
              false_iff]
            have vertical :=
              (GridSegment.isVertical_translate _ _).mp axes.2
            exact fun horizontal => vertical.2 horizontal.1

/-- Every retained carrier port has perpendicular local coordinate six and
axial local coordinate congruent to one modulo ten. -/
theorem retainedCarrierNode_localPosition_axis_data
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    if node.isHorizontal then
      node.localPosition.2 = 6 ∧ node.localPosition.1 % 10 = 1
    else
      node.localPosition.1 = 6 ∧ node.localPosition.2 % 10 = 1 := by
  cases node with
  | boundary boundary =>
      cases boundary with
      | mk crossing side =>
          cases side <;>
            norm_num [CarrierNode.isHorizontal,
              CarrierNode.localPosition, CrossingSide.localPosition,
              CrossoverVariable.position]
  | terminal terminal =>
      simp only [CarrierNode.indexed] at axisAligned
      rcases axisAligned with horizontal | vertical
      · rcases horizontal with ⟨sameY, differentX⟩
        have horizontal' :
            terminal.indexed.segment.IsHorizontal :=
          ⟨sameY, differentX⟩
        rcases lt_or_gt_of_ne differentX with forward | backward
        · simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, horizontal', forward]
          cases terminal.endpoint <;> norm_num
        · have notForward :
              ¬terminal.indexed.segment.start.1 <
                terminal.indexed.segment.finish.1 := by
            omega
          simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, horizontal', notForward,
            backward]
          cases terminal.endpoint <;> norm_num
      · rcases vertical with ⟨sameX, differentY⟩
        have notHorizontal :
            ¬terminal.indexed.segment.IsHorizontal := by
          intro horizontal
          exact differentY horizontal.1
        rcases lt_or_gt_of_ne differentY with forward | backward
        · simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, sameX, notHorizontal,
            forward]
          cases terminal.endpoint <;> norm_num
        · have notForward :
              ¬terminal.indexed.segment.start.2 <
                terminal.indexed.segment.finish.2 := by
            omega
          simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, sameX, notHorizontal,
            notForward, backward]
          cases terminal.endpoint <;> norm_num

/-- Nodes with one retained occurrence key lie on one refined axis and have
axial coordinates congruent to one modulo ten. -/
theorem retainedCarrierNode_commonCarrier_axis_data
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    if first.isHorizontal then
      (first.position graph).2 = (second.position graph).2 ∧
        (first.position graph).1 % 10 = 1 ∧
        (second.position graph).1 % 10 = 1
    else
      (first.position graph).1 = (second.position graph).1 ∧
        (first.position graph).2 % 10 = 1 ∧
        (second.position graph).2 % 10 = 1 := by
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstMem)
      (retainedCarrierNode_indexed_mem graph secondMem)
      keyEqual
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      first.indexed (retainedCarrierNode_indexed_mem graph firstMem)
  have secondAligned :
      second.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  have firstContains :=
    retainedCarrierNode_drawingPoint_contains
      graph firstMem firstAligned
  have secondContains :=
    retainedCarrierNode_drawingPoint_contains
      graph secondMem secondAligned
  have firstLocal :=
    retainedCarrierNode_localPosition_axis_data
      graph firstMem firstAligned
  have secondLocal :=
    retainedCarrierNode_localPosition_axis_data
      graph secondMem secondAligned
  by_cases horizontalTag : first.isHorizontal = true
  · rw [if_pos horizontalTag]
    have firstHorizontal :
        first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph firstMem firstAligned).mp horizontalTag
    have secondHorizontal :
        second.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    have secondHorizontalTag :
        second.isHorizontal = true :=
      (retainedCarrierNode_isHorizontal_iff
        graph secondMem secondAligned).mpr secondHorizontal
    rw [if_pos horizontalTag] at firstLocal
    rw [if_pos secondHorizontalTag] at secondLocal
    let segment :=
      first.indexed.segment.translate
        ((drawing graph).periodTranslation first.translate)
    have segmentHorizontal : segment.IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr firstHorizontal
    have secondSegmentEqual :
        second.indexed.segment.translate
            ((drawing graph).periodTranslation second.translate) =
          segment := by
      simp [segment, occurrenceEqual.1, occurrenceEqual.2]
    rw [secondSegmentEqual] at secondContains
    have firstY :
        (first.drawingPoint graph).2 = segment.start.2 := by
      rcases firstContains with horizontal | vertical
      · exact horizontal.2.1
      · exact False.elim (vertical.1.2 segmentHorizontal.1)
    have secondY :
        (second.drawingPoint graph).2 = segment.start.2 := by
      rcases secondContains with horizontal | vertical
      · exact horizontal.2.1
      · exact False.elim (vertical.1.2 segmentHorizontal.1)
    rw [CarrierNode.position_eq_scale_add_local,
      CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega
  · have firstNotHorizontal :
        ¬first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact horizontalTag
        ((retainedCarrierNode_isHorizontal_iff
          graph firstMem firstAligned).mpr horizontal)
    have firstVertical :
        first.indexed.segment.IsVertical :=
      firstAligned.resolve_left firstNotHorizontal
    have secondVertical :
        second.indexed.segment.IsVertical := by
      rw [← occurrenceEqual.1]
      exact firstVertical
    have secondNotHorizontal :
        ¬second.indexed.segment.IsHorizontal := by
      intro horizontal
      exact secondVertical.2 horizontal.1
    have secondHorizontalTag :
        second.isHorizontal = false := by
      apply Bool.eq_false_iff.mpr
      intro tag
      exact secondNotHorizontal
        ((retainedCarrierNode_isHorizontal_iff
          graph secondMem secondAligned).mp tag)
    rw [if_neg horizontalTag]
    rw [if_neg horizontalTag] at firstLocal
    rw [if_neg (by simpa using secondHorizontalTag)] at secondLocal
    let segment :=
      first.indexed.segment.translate
        ((drawing graph).periodTranslation first.translate)
    have segmentVertical : segment.IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr firstVertical
    have secondSegmentEqual :
        second.indexed.segment.translate
            ((drawing graph).periodTranslation second.translate) =
          segment := by
      simp [segment, occurrenceEqual.1, occurrenceEqual.2]
    rw [secondSegmentEqual] at secondContains
    have firstX :
        (first.drawingPoint graph).1 = segment.start.1 := by
      rcases firstContains with horizontal | vertical
      · exact False.elim (segmentVertical.2 horizontal.1.1)
      · exact vertical.2.1
    have secondX :
        (second.drawingPoint graph).1 = segment.start.1 := by
      rcases secondContains with horizontal | vertical
      · exact False.elim (segmentVertical.2 horizontal.1.1)
      · exact vertical.2.1
    rw [CarrierNode.position_eq_scale_add_local,
      CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega

end PeriodicOrthocrossing
end LeanTrominoes
