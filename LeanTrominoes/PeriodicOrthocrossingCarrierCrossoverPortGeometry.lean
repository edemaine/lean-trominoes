/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCoordinateOrder
import LeanTrominoes.PeriodicOrthocrossingCrossoverCarrierInterface
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPortGeometry

/-!
# Retained carrier interfaces at crossover boundaries

The two ports of one crossover on a common carrier are consecutive in the
strict complete-carrier order, and their internal pair is omitted.  Thus a
retained link can leave only a right or bottom boundary and can enter only a
left or top boundary.  This determines its exact crossover-facing compass
port and macrocell origin.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A retained carrier whose first endpoint is a crossover boundary leaves
through its right or bottom side. -/
theorem drawingCompleteCarrierLink_first_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    boundary.side = .right ∨ boundary.side = .bottom := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  rcases pair with ⟨first, second⟩
  simp only [carrierNodePairLink] at firstEqual
  subst first
  rcases boundary with ⟨crossing, side⟩
  cases side with
  | right =>
      exact Or.inl rfl
  | bottom =>
      exact Or.inr rfl
  | left =>
      let siblingBoundary : CrossingBoundary :=
        ⟨crossing, .right⟩
      let sibling : CarrierNode :=
        .boundary siblingBoundary
      have members :=
        mem_of_mem_consecutivePairs pairData.1
      have firstData :=
        (mem_completeCarrierNodes_iff
          graph key (.boundary ⟨crossing, .left⟩)).mp
          members.1
      have boundaryMem :
          (CrossingBoundary.mk crossing .left) ∈
            drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at firstData
        simpa using firstData.1
      have crossingMem :=
        drawingCrossingBoundary_crossing_mem_orientedCrossings
          graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈
            drawingCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ completeCarrierNodes graph key := by
        apply (mem_completeCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold drawingCarrierNodes
          exact List.mem_append_right _
            (List.mem_map.mpr
              ⟨siblingBoundary, siblingBoundaryMem, rfl⟩)
        · change
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.first crossing.firstTranslate = key
          exact firstData.2
      have firstLtSibling :
          (CarrierNode.boundary
              ⟨crossing, .left⟩).orderCoordinate graph <
            sibling.orderCoordinate graph := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
      have siblingCoordinate :
          sibling.orderCoordinate graph =
            (CarrierNode.boundary
              ⟨crossing, .left⟩).orderCoordinate graph + 10 := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
        ring
      have gap :=
        completeCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1 pairData.2
      have siblingLeSecond :
          sibling.orderCoordinate graph ≤
            second.orderCoordinate graph := by
        rw [siblingCoordinate]
        exact gap
      have siblingEqual :=
        eq_second_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (completeCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLtSibling siblingLeSecond
      have siblingEqual' : sibling = second := by
        simpa using siblingEqual
      subst second
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData
  | top =>
      let siblingBoundary : CrossingBoundary :=
        ⟨crossing, .bottom⟩
      let sibling : CarrierNode :=
        .boundary siblingBoundary
      have members :=
        mem_of_mem_consecutivePairs pairData.1
      have firstData :=
        (mem_completeCarrierNodes_iff
          graph key (.boundary ⟨crossing, .top⟩)).mp
          members.1
      have boundaryMem :
          (CrossingBoundary.mk crossing .top) ∈
            drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at firstData
        simpa using firstData.1
      have crossingMem :=
        drawingCrossingBoundary_crossing_mem_orientedCrossings
          graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈
            drawingCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ completeCarrierNodes graph key := by
        apply (mem_completeCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold drawingCarrierNodes
          exact List.mem_append_right _
            (List.mem_map.mpr
              ⟨siblingBoundary, siblingBoundaryMem, rfl⟩)
        · change
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.second crossing.secondTranslate = key
          exact firstData.2
      have firstLtSibling :
          (CarrierNode.boundary
              ⟨crossing, .top⟩).orderCoordinate graph <
            sibling.orderCoordinate graph := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
      have siblingCoordinate :
          sibling.orderCoordinate graph =
            (CarrierNode.boundary
              ⟨crossing, .top⟩).orderCoordinate graph + 10 := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
        ring
      have gap :=
        completeCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1 pairData.2
      have siblingLeSecond :
          sibling.orderCoordinate graph ≤
            second.orderCoordinate graph := by
        rw [siblingCoordinate]
        exact gap
      have siblingEqual :=
        eq_second_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (completeCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLtSibling siblingLeSecond
      have siblingEqual' : sibling = second := by
        simpa using siblingEqual
      subst second
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData

/-- A retained carrier whose second endpoint is a crossover boundary enters
through its left or top side. -/
theorem drawingCompleteCarrierLink_second_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    boundary.side = .left ∨ boundary.side = .top := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  rcases pair with ⟨first, second⟩
  simp only [carrierNodePairLink] at secondEqual
  subst second
  rcases boundary with ⟨crossing, side⟩
  cases side with
  | left =>
      exact Or.inl rfl
  | top =>
      exact Or.inr rfl
  | right =>
      let siblingBoundary : CrossingBoundary :=
        ⟨crossing, .left⟩
      let sibling : CarrierNode :=
        .boundary siblingBoundary
      have members :=
        mem_of_mem_consecutivePairs pairData.1
      have secondData :=
        (mem_completeCarrierNodes_iff
          graph key (.boundary ⟨crossing, .right⟩)).mp
          members.2
      have boundaryMem :
          (CrossingBoundary.mk crossing .right) ∈
            drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at secondData
        simpa using secondData.1
      have crossingMem :=
        drawingCrossingBoundary_crossing_mem_orientedCrossings
          graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈
            drawingCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ completeCarrierNodes graph key := by
        apply (mem_completeCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold drawingCarrierNodes
          exact List.mem_append_right _
            (List.mem_map.mpr
              ⟨siblingBoundary, siblingBoundaryMem, rfl⟩)
        · change
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.first crossing.firstTranslate = key
          exact secondData.2
      have siblingLtSecond :
          sibling.orderCoordinate graph <
            (CarrierNode.boundary
              ⟨crossing, .right⟩).orderCoordinate graph := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
      have secondCoordinate :
          (CarrierNode.boundary
              ⟨crossing, .right⟩).orderCoordinate graph =
            sibling.orderCoordinate graph + 10 := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
        ring
      have gap :=
        completeCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1 pairData.2
      have gap' :
          first.orderCoordinate graph + 10 ≤
            (CarrierNode.boundary
              ⟨crossing, .right⟩).orderCoordinate graph := by
        simpa using gap
      have firstLeSibling :
          first.orderCoordinate graph ≤
            sibling.orderCoordinate graph := by
        rw [secondCoordinate] at gap'
        omega
      have siblingEqual :=
        eq_first_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (completeCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLeSibling siblingLtSecond
      have siblingEqual' : sibling = first := by
        simpa using siblingEqual
      subst first
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData
  | bottom =>
      let siblingBoundary : CrossingBoundary :=
        ⟨crossing, .top⟩
      let sibling : CarrierNode :=
        .boundary siblingBoundary
      have members :=
        mem_of_mem_consecutivePairs pairData.1
      have secondData :=
        (mem_completeCarrierNodes_iff
          graph key (.boundary ⟨crossing, .bottom⟩)).mp
          members.2
      have boundaryMem :
          (CrossingBoundary.mk crossing .bottom) ∈
            drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at secondData
        simpa using secondData.1
      have crossingMem :=
        drawingCrossingBoundary_crossing_mem_orientedCrossings
          graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈
            drawingCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ completeCarrierNodes graph key := by
        apply (mem_completeCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold drawingCarrierNodes
          exact List.mem_append_right _
            (List.mem_map.mpr
              ⟨siblingBoundary, siblingBoundaryMem, rfl⟩)
        · change
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.second crossing.secondTranslate = key
          exact secondData.2
      have siblingLtSecond :
          sibling.orderCoordinate graph <
            (CarrierNode.boundary
              ⟨crossing, .bottom⟩).orderCoordinate graph := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
      have secondCoordinate :
          (CarrierNode.boundary
              ⟨crossing, .bottom⟩).orderCoordinate graph =
            sibling.orderCoordinate graph + 10 := by
        simp [sibling, siblingBoundary,
          CarrierNode.orderCoordinate,
          CarrierNode.isHorizontal, CarrierNode.position,
          CrossingBoundary.position, crossingMacroOrigin,
          CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale]
        ring
      have gap :=
        completeCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1 pairData.2
      have gap' :
          first.orderCoordinate graph + 10 ≤
            (CarrierNode.boundary
              ⟨crossing, .bottom⟩).orderCoordinate graph := by
        simpa using gap
      have firstLeSibling :
          first.orderCoordinate graph ≤
            sibling.orderCoordinate graph := by
        rw [secondCoordinate] at gap'
        omega
      have siblingEqual :=
        eq_first_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (completeCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLeSibling siblingLtSecond
      have siblingEqual' : sibling = first := by
        simpa using siblingEqual
      subst first
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData

/-- At a first crossover-boundary endpoint, the lens's computed compass
port is exactly that boundary side's crossover port. -/
theorem drawingCompleteCarrierLink_firstCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort := by
  have sideClass :=
    drawingCompleteCarrierLink_first_boundary_side
      wellFormed degree isLocal linkMem firstEqual
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
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

/-- At a second crossover-boundary endpoint, the lens's computed compass
port is exactly that boundary side's crossover port. -/
theorem drawingCompleteCarrierLink_secondCarrierPort_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      boundary.side.carrierPort := by
  have sideClass :=
    drawingCompleteCarrierLink_second_boundary_side
      wellFormed degree isLocal linkMem secondEqual
  have horizontalIff :=
    drawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal linkMem
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
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

/-- At a first crossover-boundary endpoint, the macrocell origin
reconstructed by the lens is the crossover's actual macrocell origin. -/
theorem drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    EqualityLink.firstCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing := by
  have portEqual :=
    drawingCompleteCarrierLink_firstCarrierPort_eq_boundary
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

/-- At a second crossover-boundary endpoint, the macrocell origin
reconstructed by the lens is the crossover's actual macrocell origin. -/
theorem drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) link =
      crossingMacroOrigin boundary.crossing := by
  have geometry :=
    drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have portEqual :=
    drawingCompleteCarrierLink_secondCarrierPort_eq_boundary
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

end PeriodicOrthocrossing
end LeanTrominoes
