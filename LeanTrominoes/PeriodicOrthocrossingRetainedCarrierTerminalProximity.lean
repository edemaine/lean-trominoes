import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierMacrocellSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierInterfaces

/-!
# Retained carriers near source-segment terminals

The first or last terminal of a source occurrence is a strict extreme of
its retained carrier chain.  Its refined axial coordinate is respectively
`20 * center + 11` or `20 * center + 1`.  Consequently, if a retained lens
on that occurrence overlaps the terminal's standard macrocell, the terminal
must be one of the lens endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A horizontal terminal's refined axial coordinate is `11` inside its
macrocell at the lower end of the segment and `1` at the upper end. -/
theorem retainedHorizontalTerminal_orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (horizontal : terminal.indexed.segment.IsHorizontal) :
    (CarrierNode.terminal terminal).orderCoordinate graph =
      planarMacroScale * (terminal.drawingPoint graph).1 +
        if terminal.IsLower then 11 else 1 := by
  rw [carrierNode_terminal_orderCoordinate_horizontal
    graph terminal horizontal]
  rcases terminal with ⟨indexed, translate, endpoint⟩
  rcases indexed with ⟨routeIndex, segmentIndex, segment⟩
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [GridSegment.IsHorizontal] at horizontal
  rcases horizontal with ⟨sameY, differentX⟩
  generalize endpointEq : endpoint = terminalEndpoint
  cases terminalEndpoint <;>
    simp [SegmentTerminal.position, SegmentTerminal.drawingPoint,
      SegmentTerminal.IsLower, segmentTerminalLocalPosition,
      planarMacroScale, Cell.add, Cell.scale, GridSegment.translate,
      sameY] <;>
    split_ifs <;> omega

/-- The analogous axial-coordinate formula for a vertical terminal. -/
theorem retainedVerticalTerminal_orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (vertical : terminal.indexed.segment.IsVertical) :
    (CarrierNode.terminal terminal).orderCoordinate graph =
      planarMacroScale * (terminal.drawingPoint graph).2 +
        if terminal.IsLower then 11 else 1 := by
  rw [carrierNode_terminal_orderCoordinate_vertical
    graph terminal vertical]
  rcases terminal with ⟨indexed, translate, endpoint⟩
  rcases indexed with ⟨routeIndex, segmentIndex, segment⟩
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [GridSegment.IsVertical] at vertical
  rcases vertical with ⟨sameX, differentY⟩
  generalize endpointEq : endpoint = terminalEndpoint
  cases terminalEndpoint <;>
    simp [SegmentTerminal.position, SegmentTerminal.drawingPoint,
      SegmentTerminal.IsLower, segmentTerminalLocalPosition,
      planarMacroScale, Cell.add, Cell.scale, GridSegment.translate,
      sameX] <;>
    split_ifs <;> omega

/-- If a raw retained lens lies on a terminal's source occurrence and
overlaps the terminal macrocell, one of its endpoints is that terminal. -/
theorem
    retainedDrawingCompleteCarrierLinkRaw_incidentToTerminal_of_key_eq_of_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    (keyEqual :
      link.first.carrierKey = terminal.carrierKey)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower
          (terminal.drawingPoint graph))
        (planarSATMacrocellRouteUpper
          (terminal.drawingPoint graph))) :
    link.first = .terminal terminal ∨
      link.second = .terminal terminal := by
  let terminalNode : CarrierNode := .terminal terminal
  have terminalNodeMem :
      terminalNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨terminal, terminalMem, rfl⟩)
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have commonKey :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have firstKey :
      link.first.carrierKey = terminalNode.carrierKey := by
    simpa [terminalNode, CarrierNode.carrierKey] using keyEqual
  have secondKey :
      link.second.carrierKey = terminalNode.carrierKey :=
    commonKey.symm.trans firstKey
  have firstTerminalAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal endpoints.1 terminalNodeMem firstKey
  have secondTerminalAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal endpoints.2 terminalNodeMem secondKey
  have terminalAligned :
      terminal.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      terminal.indexed
      (drawingSegmentTerminal_indexed_mem graph terminalMem).1
  by_cases horizontal : link.first.isHorizontal = true
  · have terminalHorizontalBool :
        terminalNode.isHorizontal = true :=
      (retainedCarrierNode_isHorizontal_iff_of_commonCarrier
        wellFormed degree isLocal endpoints.1 terminalNodeMem
        firstKey).mp horizontal
    have terminalHorizontal :
        terminal.indexed.segment.IsHorizontal := by
      exact
        (retainedCarrierNode_isHorizontal_iff
          graph terminalNodeMem terminalAligned).mp
            terminalHorizontalBool
    have secondHorizontal :
        link.second.isHorizontal = true :=
      (retainedCarrierNode_isHorizontal_iff_of_commonCarrier
        wellFormed degree isLocal endpoints.1 endpoints.2
        commonKey).mp horizontal
    rw [if_pos horizontal] at firstTerminalAxis
    rw [if_pos secondHorizontal] at secondTerminalAxis
    have firstMod :
        link.first.orderCoordinate graph % 10 = 1 := by
      simpa [CarrierNode.orderCoordinate, horizontal] using
        firstTerminalAxis.2.1
    have secondMod :
        link.second.orderCoordinate graph % 10 = 1 := by
      simpa [CarrierNode.orderCoordinate, secondHorizontal] using
        secondTerminalAxis.2.1
    have overlapData :=
      retainedDrawingCompleteCarrierLinkRaw_horizontal_macrocell_overlap_data
        wellFormed degree isLocal linkMem horizontal
        (terminal.drawingPoint graph) notSeparated
    have firstUpper :
        link.first.orderCoordinate graph ≤
          planarMacroScale * (terminal.drawingPoint graph).1 + 13 := by
      simpa [CarrierNode.orderCoordinate, horizontal] using
        overlapData.2.1
    have secondLower :
        planarMacroScale * (terminal.drawingPoint graph).1 ≤
          link.second.orderCoordinate graph := by
      simpa [CarrierNode.orderCoordinate, secondHorizontal] using
        overlapData.2.2
    by_cases lower : terminal.IsLower
    · by_cases firstEqual :
          link.first = terminalNode
      · exact Or.inl (by simpa [terminalNode] using firstEqual)
      · have extreme :=
          retainedCarrierNode_terminal_extreme
            wellFormed degree isLocal terminalMem endpoints.1
            firstKey firstEqual
        rw [if_pos lower] at extreme
        have terminalCoordinate :=
          retainedHorizontalTerminal_orderCoordinate
            graph terminal terminalHorizontal
        rw [if_pos lower] at terminalCoordinate
        simp only [planarMacroScale] at firstMod firstUpper terminalCoordinate extreme
        omega
    · by_cases secondEqual :
          link.second = terminalNode
      · exact Or.inr (by simpa [terminalNode] using secondEqual)
      · have extreme :=
          retainedCarrierNode_terminal_extreme
            wellFormed degree isLocal terminalMem endpoints.2
            secondKey secondEqual
        rw [if_neg lower] at extreme
        have terminalCoordinate :=
          retainedHorizontalTerminal_orderCoordinate
            graph terminal terminalHorizontal
        rw [if_neg lower] at terminalCoordinate
        simp only [planarMacroScale] at secondMod secondLower terminalCoordinate extreme
        omega
  · have terminalVertical :
        terminal.indexed.segment.IsVertical := by
      exact terminalAligned.resolve_left fun terminalHorizontal =>
        horizontal
          ((retainedCarrierNode_isHorizontal_iff_of_commonCarrier
            wellFormed degree isLocal endpoints.1 terminalNodeMem
            firstKey).mpr
              ((retainedCarrierNode_isHorizontal_iff
                graph terminalNodeMem terminalAligned).mpr
                  terminalHorizontal))
    have secondVertical :
        ¬link.second.isHorizontal = true := by
      intro secondHorizontal
      exact horizontal
        ((retainedCarrierNode_isHorizontal_iff_of_commonCarrier
          wellFormed degree isLocal endpoints.1 endpoints.2
          commonKey).mpr secondHorizontal)
    rw [if_neg horizontal] at firstTerminalAxis
    rw [if_neg secondVertical] at secondTerminalAxis
    have firstMod :
        link.first.orderCoordinate graph % 10 = 1 := by
      simpa [CarrierNode.orderCoordinate, horizontal] using
        firstTerminalAxis.2.1
    have secondMod :
        link.second.orderCoordinate graph % 10 = 1 := by
      simpa [CarrierNode.orderCoordinate, secondVertical] using
        secondTerminalAxis.2.1
    have overlapData :=
      retainedDrawingCompleteCarrierLinkRaw_vertical_macrocell_overlap_data
        wellFormed degree isLocal linkMem horizontal
        (terminal.drawingPoint graph) notSeparated
    have firstUpper :
        link.first.orderCoordinate graph ≤
          planarMacroScale * (terminal.drawingPoint graph).2 + 13 := by
      simpa [CarrierNode.orderCoordinate, horizontal] using
        overlapData.2.1
    have secondLower :
        planarMacroScale * (terminal.drawingPoint graph).2 ≤
          link.second.orderCoordinate graph := by
      simpa [CarrierNode.orderCoordinate, secondVertical] using
        overlapData.2.2
    by_cases lower : terminal.IsLower
    · by_cases firstEqual :
          link.first = terminalNode
      · exact Or.inl (by simpa [terminalNode] using firstEqual)
      · have extreme :=
          retainedCarrierNode_terminal_extreme
            wellFormed degree isLocal terminalMem endpoints.1
            firstKey firstEqual
        rw [if_pos lower] at extreme
        have terminalCoordinate :=
          retainedVerticalTerminal_orderCoordinate
            graph terminal terminalVertical
        rw [if_pos lower] at terminalCoordinate
        simp only [planarMacroScale] at firstMod firstUpper terminalCoordinate extreme
        omega
    · by_cases secondEqual :
          link.second = terminalNode
      · exact Or.inr (by simpa [terminalNode] using secondEqual)
      · have extreme :=
          retainedCarrierNode_terminal_extreme
            wellFormed degree isLocal terminalMem endpoints.2
            secondKey secondEqual
        rw [if_neg lower] at extreme
        have terminalCoordinate :=
          retainedVerticalTerminal_orderCoordinate
            graph terminal terminalVertical
        rw [if_neg lower] at terminalCoordinate
        simp only [planarMacroScale] at secondMod secondLower terminalCoordinate extreme
        omega

/-- The matched-terminal incidence theorem for selected representatives. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToTerminal_of_key_eq_of_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    (keyEqual :
      link.first.carrierKey = terminal.carrierKey)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower
          (terminal.drawingPoint graph))
        (planarSATMacrocellRouteUpper
          (terminal.drawingPoint graph))) :
    link.first = .terminal terminal ∨
      link.second = .terminal terminal :=
  retainedDrawingCompleteCarrierLinkRaw_incidentToTerminal_of_key_eq_of_overlap
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      terminalMem keyEqual notSeparated

end PeriodicOrthocrossing
end LeanTrominoes
