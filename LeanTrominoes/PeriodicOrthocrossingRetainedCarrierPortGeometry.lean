/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierInterfaces
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossoverPortGeometry

/-!
# Exact ports of selected retained carrier links

The endpoint classifications for the finite retained carrier family determine
the exact compass port and macrocell origin exposed by every selected equality
lens.  These identities let the generic lens drawing meet crossover, bend, and
route-terminal component drawings at their certified interfaces.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- At a first raw retained crossover-boundary endpoint, the lens's computed
compass port is exactly that boundary side's crossover port. -/
theorem retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort := by
  have sideClass :=
    retainedDrawingCompleteCarrierLinkRaw_first_boundary_side
      wellFormed degree isLocal linkMem firstEqual
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
      wellFormed degree isLocal linkMem
  rcases boundary with ⟨crossing, side⟩
  cases side with
  | left =>
      simp at sideClass
  | top =>
      simp at sideClass
  | right =>
      unfold CarrierNode.HasForwardClearance at clearance
      rw [firstEqual] at clearance
      simp [CarrierNode.isHorizontal] at clearance
      have xLt :
          ((CarrierNode.boundary
              ⟨crossing, .right⟩).position graph).1 <
            (link.second.position graph).1 := by
        omega
      simp [EqualityLink.firstCarrierPort,
        EqualityLink.carrierDirection,
        AxisDirection.between, firstEqual,
        clearance.1, xLt, CrossingSide.carrierPort,
        AxisDirection.firstCarrierPort]
  | bottom =>
      unfold CarrierNode.HasForwardClearance at clearance
      rw [firstEqual] at clearance
      simp [CarrierNode.isHorizontal] at clearance
      have yLt :
          ((CarrierNode.boundary
              ⟨crossing, .bottom⟩).position graph).2 <
            (link.second.position graph).2 := by
        omega
      have yNe :
          ((CarrierNode.boundary
              ⟨crossing, .bottom⟩).position graph).2 ≠
            (link.second.position graph).2 :=
        ne_of_lt yLt
      simp [EqualityLink.firstCarrierPort,
        EqualityLink.carrierDirection,
        AxisDirection.between, firstEqual,
        clearance.1, yLt, yNe,
        CrossingSide.carrierPort,
        AxisDirection.firstCarrierPort]

/-- The first-boundary port identity for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort :=
  retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_boundary
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 firstEqual

/-- At a second raw retained crossover-boundary endpoint, the lens's
computed compass port is exactly that boundary side's crossover port. -/
theorem retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort := by
  have sideClass :=
    retainedDrawingCompleteCarrierLinkRaw_second_boundary_side
      wellFormed degree isLocal linkMem secondEqual
  have horizontalIff :=
    retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
      wellFormed degree isLocal linkMem
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
      wellFormed degree isLocal linkMem
  rcases boundary with ⟨crossing, side⟩
  cases side with
  | right =>
      simp at sideClass
  | bottom =>
      simp at sideClass
  | left =>
      have horizontalTag :
          link.first.isHorizontal = true := by
        apply horizontalIff.mpr
        rw [secondEqual]
        rfl
      unfold CarrierNode.HasForwardClearance at clearance
      rw [if_pos horizontalTag] at clearance
      have xLt :
          (link.first.position graph).1 <
            ((CarrierNode.boundary
              ⟨crossing, .left⟩).position graph).1 := by
        rw [← secondEqual]
        omega
      simp [EqualityLink.secondCarrierPort,
        EqualityLink.carrierDirection,
        AxisDirection.between, secondEqual,
        clearance.1, xLt, CrossingSide.carrierPort,
        AxisDirection.secondCarrierPort]
  | top =>
      have notHorizontalTag :
          ¬link.first.isHorizontal = true := by
        intro horizontalTag
        have secondHorizontal := horizontalIff.mp horizontalTag
        rw [secondEqual] at secondHorizontal
        simp [CarrierNode.isHorizontal] at secondHorizontal
      unfold CarrierNode.HasForwardClearance at clearance
      rw [if_neg notHorizontalTag] at clearance
      have yLt :
          (link.first.position graph).2 <
            ((CarrierNode.boundary
              ⟨crossing, .top⟩).position graph).2 := by
        rw [← secondEqual]
        omega
      have yNe :
          (link.first.position graph).2 ≠
            ((CarrierNode.boundary
              ⟨crossing, .top⟩).position graph).2 :=
        ne_of_lt yLt
      simp [EqualityLink.secondCarrierPort,
        EqualityLink.carrierDirection,
        AxisDirection.between, secondEqual,
        clearance.1, yLt, yNe,
        CrossingSide.carrierPort,
        AxisDirection.secondCarrierPort]

/-- The second-boundary port identity for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort :=
  retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_boundary
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

/-- Every terminal endpoint of a raw retained link is one of the
drawing's segment terminals. -/
theorem retainedDrawingCompleteCarrierLinkRaw_terminal_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal ∈ drawingSegmentTerminals graph := by
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  rcases incident with incident | incident
  · rw [incident] at endpoints
    rcases List.mem_append.mp endpoints.1 with
      terminalMem | boundaryMem
    · simpa using terminalMem
    · simp at boundaryMem
  · rw [incident] at endpoints
    rcases List.mem_append.mp endpoints.2 with
      terminalMem | boundaryMem
    · simpa using terminalMem
    · simp at boundaryMem

/-- The endpoints of every raw retained link are distinct. -/
theorem retainedDrawingCompleteCarrierLinkRaw_endpoints_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    link.first ≠ link.second :=
  (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
    wellFormed degree isLocal linkMem).different

/-- A terminal endpoint of a raw retained link belongs to a genuine
orthogonal source segment. -/
theorem retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal.indexed.segment.IsAxisAligned := by
  have terminalMem :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_mem
      graph linkMem incident
  exact
    drawing_isOrthogonal wellFormed isLocal degree
      terminal.indexed
      (drawingSegmentTerminal_indexed_mem
        graph terminalMem).1

/-- A first terminal endpoint of a raw retained link is lower. -/
theorem retainedDrawingCompleteCarrierLinkRaw_first_terminal_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    terminal.IsLower := by
  have terminalMem :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_mem
      graph linkMem (Or.inl firstEqual)
  have oriented :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_orientation
      wellFormed degree isLocal terminalMem linkMem
        (Or.inl firstEqual)
  by_contra notLower
  rw [if_neg notLower] at oriented
  exact
    (retainedDrawingCompleteCarrierLinkRaw_endpoints_ne
      wellFormed degree isLocal linkMem)
      (firstEqual.trans oriented.symm)

/-- A second terminal endpoint of a raw retained link is upper. -/
theorem retainedDrawingCompleteCarrierLinkRaw_second_terminal_not_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    ¬terminal.IsLower := by
  intro lower
  have terminalMem :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_mem
      graph linkMem (Or.inr secondEqual)
  have oriented :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_orientation
      wellFormed degree isLocal terminalMem linkMem
        (Or.inr secondEqual)
  rw [if_pos lower] at oriented
  exact
    (retainedDrawingCompleteCarrierLinkRaw_endpoints_ne
      wellFormed degree isLocal linkMem)
      (oriented.trans secondEqual.symm)

/-- At a first retained terminal endpoint, the computed compass port is the
terminal's increasing-coordinate carrier port. -/
theorem retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort := by
  have lower :=
    retainedDrawingCompleteCarrierLinkRaw_first_terminal_isLower
      wellFormed degree isLocal linkMem firstEqual
  have aligned :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inl firstEqual)
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
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

/-- At a second retained terminal endpoint, the terminal source segment is
horizontal exactly when the first carrier node has the horizontal tag. -/
theorem retainedDrawingCompleteCarrierLinkRaw_second_terminal_horizontal_iff
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    link.first.isHorizontal = true ↔
      terminal.indexed.segment.IsHorizontal := by
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have common :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have terminalMem :
      CarrierNode.terminal terminal ∈ retainedDrawingCarrierNodes graph := by
    simpa [secondEqual] using endpoints.2
  have keyEqual :
      link.first.carrierKey =
        (CarrierNode.terminal terminal).carrierKey := by
    simpa [secondEqual] using common
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph endpoints.1)
      (retainedCarrierNode_indexed_mem graph terminalMem)
      keyEqual
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (retainedCarrierNode_indexed_mem graph endpoints.1)
  have secondAligned :
      terminal.indexed.segment.IsAxisAligned := by
    have aligned := firstAligned
    rw [occurrenceEqual.1] at aligned
    simpa [CarrierNode.indexed] using aligned
  constructor
  · intro horizontalTag
    have firstHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mp horizontalTag
    rw [occurrenceEqual.1] at firstHorizontal
    simpa [CarrierNode.indexed] using firstHorizontal
  · intro terminalHorizontal
    apply
      (retainedCarrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mpr
    rw [occurrenceEqual.1]
    simpa [CarrierNode.indexed] using terminalHorizontal

/-- At a second retained terminal endpoint, the computed compass port is the
terminal's increasing-coordinate carrier port. -/
theorem retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort := by
  have notLower :=
    retainedDrawingCompleteCarrierLinkRaw_second_terminal_not_isLower
      wellFormed degree isLocal linkMem secondEqual
  have aligned :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
      wellFormed degree isLocal linkMem (Or.inr secondEqual)
  have horizontalIff :=
    retainedDrawingCompleteCarrierLinkRaw_second_terminal_horizontal_iff
      wellFormed degree isLocal linkMem secondEqual
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
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

/-- The first lens macrocell origin at a raw retained crossover boundary is
the crossover's actual macrocell origin. -/
theorem retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing := by
  have portEqual :=
    retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_boundary
      wellFormed degree isLocal linkMem firstEqual
  have reconstruct :=
    EqualityLink.add_firstCarrierMacroOrigin_portPosition
      (CarrierNode.position graph) link
  rw [portEqual, firstEqual] at reconstruct
  change
    Cell.add
        (EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link)
        boundary.side.carrierPort.position =
      Cell.add
        (crossingMacroOrigin boundary.crossing)
        boundary.side.localPosition
    at reconstruct
  rw [boundary.side.carrierPort_position] at reconstruct
  exact Cell.add_right_injective _ reconstruct

/-- The first-boundary macrocell-origin identity for selected
representatives. -/
theorem retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing :=
  retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 firstEqual

/-- The second lens macrocell origin at a raw retained crossover boundary is
the crossover's actual macrocell origin. -/
theorem retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing := by
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal linkMem
  have portEqual :=
    retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_boundary
      wellFormed degree isLocal linkMem secondEqual
  have reconstruct :=
    EqualityLink.add_secondCarrierMacroOrigin_portPosition geometry
  rw [portEqual, secondEqual] at reconstruct
  change
    Cell.add
        (EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link)
        boundary.side.carrierPort.position =
      Cell.add
        (crossingMacroOrigin boundary.crossing)
        boundary.side.localPosition
    at reconstruct
  rw [boundary.side.carrierPort_position] at reconstruct
  exact Cell.add_right_injective _ reconstruct

/-- The second-boundary macrocell-origin identity for selected
representatives. -/
theorem retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing :=
  retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

/-- The first lens macrocell origin at a retained terminal is exactly its
scaled drawing cell. -/
theorem retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) := by
  have portEqual :=
    retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_terminal
      wellFormed degree isLocal linkMem firstEqual
  have aligned :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
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

/-- The second lens macrocell origin at a retained terminal is exactly its
scaled drawing cell. -/
theorem retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) := by
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal linkMem
  have portEqual :=
    retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_terminal
      wellFormed degree isLocal linkMem secondEqual
  have aligned :=
    retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
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

/-! ## Selected-representative compatibility wrappers -/

/-- Terminal membership for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_terminal_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal ∈ drawingSegmentTerminals graph :=
  retainedDrawingCompleteCarrierLinkRaw_terminal_mem graph
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1 incident

/-- Endpoint distinctness for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_endpoints_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    link.first ≠ link.second :=
  retainedDrawingCompleteCarrierLinkRaw_endpoints_ne
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1

/-- Terminal-axis alignment for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_terminal_axisAligned
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal.indexed.segment.IsAxisAligned :=
  retainedDrawingCompleteCarrierLinkRaw_terminal_axisAligned
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 incident

/-- First-terminal orientation for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_first_terminal_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    terminal.IsLower :=
  retainedDrawingCompleteCarrierLinkRaw_first_terminal_isLower
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 firstEqual

/-- Second-terminal orientation for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_second_terminal_not_isLower
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    ¬terminal.IsLower :=
  retainedDrawingCompleteCarrierLinkRaw_second_terminal_not_isLower
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

/-- First-terminal port identity for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort :=
  retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_terminal
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 firstEqual

/-- Second-terminal axis identity for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_second_terminal_horizontal_iff
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    link.first.isHorizontal = true ↔
      terminal.indexed.segment.IsHorizontal :=
  retainedDrawingCompleteCarrierLinkRaw_second_terminal_horizontal_iff
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

/-- Second-terminal port identity for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      terminal.carrierPort :=
  retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_terminal
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

/-- First-terminal macrocell-origin identity for selected
representatives. -/
theorem retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEqual : link.first = .terminal terminal) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_terminal
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 firstEqual

/-- Second-terminal macrocell-origin identity for selected
representatives. -/
theorem retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (secondEqual : link.second = .terminal terminal) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      Cell.scale planarMacroScale (terminal.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_terminal
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 secondEqual

end PeriodicOrthocrossing
end LeanTrominoes
