/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingBendCornerGeometry
import LeanTrominoes.PlanarThreeSATEqualityLensCarrierInterface

/-!
# Carrier-lens ports at segment terminals

A retained complete-carrier link is directed in increasing drawing
coordinate.  At a terminal endpoint, that order determines exactly which
compass port the lens occupies.  This file identifies that computed lens
port and macrocell origin with the corresponding incoming or outgoing port
of a route-bend corner drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The four local corner-port positions are pairwise distinct. -/
theorem CornerPort.position_injective :
    Function.Injective CornerPort.position := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [CornerPort.position]

/-- Compass port through which a complete carrier leaves a terminal
macrocell in increasing drawing-coordinate order. -/
def SegmentTerminal.carrierPort
    (terminal : SegmentTerminal) : CornerPort :=
  if terminal.indexed.segment.IsHorizontal then
    if terminal.IsLower then .east else .west
  else if terminal.IsLower then .north else .south

/-- A lower endpoint of a horizontal segment uses the east port. -/
theorem segmentTerminalLocalPosition_eq_east_of_isLower
    (terminal : SegmentTerminal)
    (horizontal : terminal.indexed.segment.IsHorizontal)
    (lower : terminal.IsLower) :
    segmentTerminalLocalPosition
        terminal.indexed.segment terminal.endpoint =
      CornerPort.east.position := by
  rcases horizontal with ⟨sameY, differentX⟩
  rcases terminal with ⟨indexed, translate, endpoint⟩
  cases endpoint <;>
    simp only [SegmentTerminal.IsLower] at lower <;>
    simp [segmentTerminalLocalPosition,
      CornerPort.position] <;>
    split_ifs <;> simp_all <;> omega

/-- An upper endpoint of a horizontal segment uses the west port. -/
theorem segmentTerminalLocalPosition_eq_west_of_not_isLower
    (terminal : SegmentTerminal)
    (horizontal : terminal.indexed.segment.IsHorizontal)
    (notLower : ¬terminal.IsLower) :
    segmentTerminalLocalPosition
        terminal.indexed.segment terminal.endpoint =
      CornerPort.west.position := by
  rcases horizontal with ⟨sameY, differentX⟩
  rcases terminal with ⟨indexed, translate, endpoint⟩
  cases endpoint <;>
    simp only [SegmentTerminal.IsLower] at notLower <;>
    simp [segmentTerminalLocalPosition,
      CornerPort.position] <;>
    split_ifs <;> simp_all <;> omega

/-- A lower endpoint of a vertical segment uses the north port. -/
theorem segmentTerminalLocalPosition_eq_north_of_isLower
    (terminal : SegmentTerminal)
    (vertical : terminal.indexed.segment.IsVertical)
    (lower : terminal.IsLower) :
    segmentTerminalLocalPosition
        terminal.indexed.segment terminal.endpoint =
      CornerPort.north.position := by
  rcases vertical with ⟨sameX, differentY⟩
  rcases terminal with ⟨indexed, translate, endpoint⟩
  cases endpoint <;>
    simp only [SegmentTerminal.IsLower] at lower <;>
    simp [segmentTerminalLocalPosition,
      CornerPort.position] <;>
    split_ifs <;> simp_all <;> omega

/-- An upper endpoint of a vertical segment uses the south port. -/
theorem segmentTerminalLocalPosition_eq_south_of_not_isLower
    (terminal : SegmentTerminal)
    (vertical : terminal.indexed.segment.IsVertical)
    (notLower : ¬terminal.IsLower) :
    segmentTerminalLocalPosition
        terminal.indexed.segment terminal.endpoint =
      CornerPort.south.position := by
  rcases vertical with ⟨sameX, differentY⟩
  rcases terminal with ⟨indexed, translate, endpoint⟩
  cases endpoint <;>
    simp only [SegmentTerminal.IsLower] at notLower <;>
    simp [segmentTerminalLocalPosition,
      CornerPort.position] <;>
    split_ifs <;> simp_all <;> omega

/-- The terminal carrier-port definition realizes the terminal's existing
local position on every genuine orthogonal segment. -/
theorem SegmentTerminal.carrierPort_position
    (terminal : SegmentTerminal)
    (aligned : terminal.indexed.segment.IsAxisAligned) :
    terminal.carrierPort.position =
      segmentTerminalLocalPosition
        terminal.indexed.segment terminal.endpoint := by
  rcases aligned with horizontal | vertical
  · by_cases lower : terminal.IsLower
    · simp [SegmentTerminal.carrierPort, horizontal, lower,
        segmentTerminalLocalPosition_eq_east_of_isLower
          terminal horizontal lower]
    · simp [SegmentTerminal.carrierPort, horizontal, lower,
        segmentTerminalLocalPosition_eq_west_of_not_isLower
          terminal horizontal lower]
  · have notHorizontal :
        ¬terminal.indexed.segment.IsHorizontal := by
      intro horizontal
      exact vertical.2 horizontal.1
    by_cases lower : terminal.IsLower
    · simp [SegmentTerminal.carrierPort, notHorizontal, lower,
        segmentTerminalLocalPosition_eq_north_of_isLower
          terminal vertical lower]
    · simp [SegmentTerminal.carrierPort, notHorizontal, lower,
        segmentTerminalLocalPosition_eq_south_of_not_isLower
          terminal vertical lower]

/-- Membership in the aggregate retained carrier family recovers the
forward-clearance fact of the underlying consecutive node pair. -/
theorem drawingCompleteCarrierLink_hasForwardClearance
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    link.first.HasForwardClearance graph link.second := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  exact completeCarrierPair_hasForwardClearance
    wellFormed degree isLocal key pairData.1 pairData.2

/-- The aggregate carrier family inherits the terminal endpoint orientation
theorem from the corresponding terminal chain. -/
theorem drawingCompleteCarrierLink_terminal_orientation
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    if terminal.IsLower then
      link.first = .terminal terminal
    else
      link.second = .terminal terminal := by
  exact
    completeCarrierLink_terminal_orientation
      wellFormed degree isLocal
      (drawingCompleteCarrierLink_terminal_mem
        graph linkMem incident)
      (drawingCompleteCarrierLink_mem_terminal_chain
        graph linkMem incident)
      incident

/-- Every terminal endpoint of a represented complete-carrier link belongs
to a genuine orthogonal source segment. -/
theorem drawingCompleteCarrierLink_terminal_axisAligned
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal.indexed.segment.IsAxisAligned := by
  have terminalMem :=
    drawingCompleteCarrierLink_terminal_mem
      graph linkMem incident
  exact
    drawing_isOrthogonal wellFormed isLocal degree
      terminal.indexed
      (drawingSegmentTerminal_indexed_mem
        graph terminalMem).1

/-- A terminal occurring as the first endpoint of a retained carrier link
is the lower terminal of its source segment. -/
theorem drawingCompleteCarrierLink_first_terminal_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    terminal.IsLower := by
  have oriented :=
    drawingCompleteCarrierLink_terminal_orientation
      wellFormed degree isLocal linkMem (Or.inl firstEqual)
  by_contra notLower
  rw [if_neg notLower] at oriented
  exact
    (drawingCompleteCarrierLink_endpoints_ne graph linkMem)
      (firstEqual.trans oriented.symm)

/-- A terminal occurring as the second endpoint of a retained carrier link
is the upper terminal of its source segment. -/
theorem drawingCompleteCarrierLink_second_terminal_not_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    ¬terminal.IsLower := by
  intro lower
  have oriented :=
    drawingCompleteCarrierLink_terminal_orientation
      wellFormed degree isLocal linkMem (Or.inr secondEqual)
  rw [if_pos lower] at oriented
  exact
    (drawingCompleteCarrierLink_endpoints_ne graph linkMem)
      (oriented.trans secondEqual.symm)

/-- At a first terminal endpoint, the lens's computed compass port is the
terminal's increasing-coordinate carrier port. -/
theorem drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort := by
  have lower :=
    drawingCompleteCarrierLink_first_terminal_isLower
      wellFormed degree isLocal linkMem firstEqual
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inl firstEqual)
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  rw [firstEqual] at clearance
  rcases aligned with horizontal | vertical
  · simp [CarrierNode.HasForwardClearance,
      CarrierNode.isHorizontal, horizontal] at clearance
    have xLt :
        ((CarrierNode.terminal terminal).position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      SegmentTerminal.carrierPort, horizontal, lower,
      AxisDirection.firstCarrierPort, firstEqual]
  · have notHorizontal :
        ¬terminal.indexed.segment.IsHorizontal := by
      intro horizontal
      exact vertical.2 horizontal.1
    simp [CarrierNode.HasForwardClearance,
      CarrierNode.isHorizontal, notHorizontal] at clearance
    have yLt :
        ((CarrierNode.terminal terminal).position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        ((CarrierNode.terminal terminal).position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      SegmentTerminal.carrierPort, notHorizontal, lower,
      AxisDirection.firstCarrierPort, firstEqual]

/-- At a second terminal endpoint, the terminal source segment is horizontal
exactly when the link's first carrier node has the horizontal axis tag. -/
theorem drawingCompleteCarrierLink_second_terminal_horizontal_iff
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    link.first.isHorizontal = true ↔
      terminal.indexed.segment.IsHorizontal := by
  have endpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph linkMem
  have common :=
    drawingCompleteCarrierLinks_common_key graph linkMem
  have terminalMem :
      CarrierNode.terminal terminal ∈ drawingCarrierNodes graph := by
    simpa [secondEqual] using endpoints.2
  have keyEqual :
      link.first.carrierKey =
        (CarrierNode.terminal terminal).carrierKey := by
    simpa [secondEqual] using common
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph endpoints.1 terminalMem keyEqual
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (carrierNode_indexed_mem graph endpoints.1)
  constructor
  · intro horizontalTag
    have firstHorizontal :=
      (carrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mp horizontalTag
    rw [occurrenceEqual.1] at firstHorizontal
    exact firstHorizontal
  · intro terminalHorizontal
    apply
      (carrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mpr
    rw [occurrenceEqual.1]
    exact terminalHorizontal

/-- At a second terminal endpoint, the lens's computed compass port is the
terminal's increasing-coordinate carrier port. -/
theorem drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort := by
  have notLower :=
    drawingCompleteCarrierLink_second_terminal_not_isLower
      wellFormed degree isLocal linkMem secondEqual
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inr secondEqual)
  have horizontalIff :=
    drawingCompleteCarrierLink_second_terminal_horizontal_iff
      wellFormed degree isLocal linkMem secondEqual
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontalTag : link.first.isHorizontal = true
  · have horizontal : terminal.indexed.segment.IsHorizontal :=
      horizontalIff.mp horizontalTag
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontalTag] at clearance
    have xLt :
        (link.first.position graph).1 <
          ((CarrierNode.terminal terminal).position graph).1 := by
      rw [← secondEqual]
      omega
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      SegmentTerminal.carrierPort, horizontal, notLower,
      AxisDirection.secondCarrierPort, secondEqual]
  · have notHorizontal :
        ¬terminal.indexed.segment.IsHorizontal := by
      intro horizontal
      exact horizontalTag (horizontalIff.mpr horizontal)
    have vertical :
        terminal.indexed.segment.IsVertical :=
      aligned.resolve_left notHorizontal
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontalTag] at clearance
    have yLt :
        (link.first.position graph).2 <
          ((CarrierNode.terminal terminal).position graph).2 := by
      rw [← secondEqual]
      omega
    have yNe :
        (link.first.position graph).2 ≠
          ((CarrierNode.terminal terminal).position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      SegmentTerminal.carrierPort, notHorizontal, notLower,
      AxisDirection.secondCarrierPort, secondEqual]

/-- Adding a fixed cell on the right is injective. -/
theorem Cell.add_right_injective (offset : Cell) :
    Function.Injective (fun point => Cell.add point offset) := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [Cell.add] at equal ⊢
  exact equal

/-- At a first terminal endpoint, the macrocell origin reconstructed by the
lens is exactly the scaled drawing cell of that terminal. -/
theorem drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) := by
  have portEqual :=
    drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
      wellFormed degree isLocal linkMem firstEqual
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inl firstEqual)
  have reconstruct :=
    EqualityLink.add_firstCarrierMacroOrigin_portPosition
      (CarrierNode.position graph) link
  rw [portEqual, firstEqual,
    CarrierNode.position_eq_scale_add_local] at reconstruct
  change
    Cell.add
        (EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link)
        terminal.carrierPort.position =
      Cell.add
        (Cell.scale planarMacroScale (terminal.drawingPoint graph))
        (segmentTerminalLocalPosition
          terminal.indexed.segment terminal.endpoint)
    at reconstruct
  rw [terminal.carrierPort_position aligned] at reconstruct
  exact Cell.add_right_injective _ reconstruct

/-- At a second terminal endpoint, the macrocell origin reconstructed by the
lens is exactly the scaled drawing cell of that terminal. -/
theorem drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) := by
  have geometry :=
    drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have portEqual :=
    drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
      wellFormed degree isLocal linkMem secondEqual
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inr secondEqual)
  have reconstruct :=
    EqualityLink.add_secondCarrierMacroOrigin_portPosition geometry
  rw [portEqual, secondEqual,
    CarrierNode.position_eq_scale_add_local] at reconstruct
  change
    Cell.add
        (EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link)
        terminal.carrierPort.position =
      Cell.add
        (Cell.scale planarMacroScale (terminal.drawingPoint graph))
        (segmentTerminalLocalPosition
          terminal.indexed.segment terminal.endpoint)
    at reconstruct
  rw [terminal.carrierPort_position aligned] at reconstruct
  exact Cell.add_right_injective _ reconstruct

/-- The incoming corner port is the increasing-coordinate carrier port of
the bend's incoming terminal. -/
theorem RouteBend.incomingTerminal_carrierPort_eq
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry) :
    routeBend.incomingTerminal.carrierPort =
      routeBend.incomingPort := by
  apply CornerPort.position_injective
  rw [routeBend.incomingTerminal.carrierPort_position
    (by
      simpa [RouteBend.incomingTerminal] using
        geometry.incomingAligned)]
  simpa [RouteBend.incomingTerminal,
    RouteBend.incomingPort] using
    segmentTerminalLocalPosition_finish_eq_cornerPort
      (GridSegment.mk routeBend.incomingStart routeBend.bend)
      geometry.incomingAligned

/-- The outgoing corner port is the increasing-coordinate carrier port of
the bend's outgoing terminal. -/
theorem RouteBend.outgoingTerminal_carrierPort_eq
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry) :
    routeBend.outgoingTerminal.carrierPort =
      routeBend.outgoingPort := by
  apply CornerPort.position_injective
  rw [routeBend.outgoingTerminal.carrierPort_position
    (by
      simpa [RouteBend.outgoingTerminal] using
        geometry.outgoingAligned)]
  simpa [RouteBend.outgoingTerminal,
    RouteBend.outgoingPort] using
    segmentTerminalLocalPosition_start_eq_cornerPort
      (GridSegment.mk routeBend.bend routeBend.outgoingFinish)
      geometry.outgoingAligned

/-- If a carrier link starts at a bend's incoming terminal, its first
boundary interface is exactly the incoming corner interface. -/
theorem drawingCompleteCarrierLink_first_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.first = .terminal routeBend.incomingTerminal) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position graph) link =
        routeBend.incomingPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- If a carrier link starts at a bend's outgoing terminal, its first
boundary interface is exactly the outgoing corner interface. -/
theorem drawingCompleteCarrierLink_first_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.first = .terminal routeBend.outgoingTerminal) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position graph) link =
        routeBend.outgoingPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- If a carrier link ends at a bend's incoming terminal, its second
boundary interface is exactly the incoming corner interface. -/
theorem drawingCompleteCarrierLink_second_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.second = .terminal routeBend.incomingTerminal) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position graph) link =
        routeBend.incomingPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- If a carrier link ends at a bend's outgoing terminal, its second
boundary interface is exactly the outgoing corner interface. -/
theorem drawingCompleteCarrierLink_second_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.second = .terminal routeBend.outgoingTerminal) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position graph) link =
        routeBend.outgoingPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

end PeriodicOrthocrossing
end LeanTrominoes
