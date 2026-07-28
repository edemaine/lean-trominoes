import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLensGeometry

/-!
# Endpoint interfaces of retained carrier links

Both ports of every retained crossover occur in the same strict carrier
chain, while the pair internal to that crossover is filtered out.  Therefore
a retained equality lens can leave a crossover only through its forward
boundary and enter one only through its backward boundary.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A raw retained carrier link whose first endpoint is a crossover boundary
leaves through the right or bottom side. -/
theorem retainedDrawingCompleteCarrierLinkRaw_first_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
        (mem_retainedCompleteCarrierNodes_iff
          graph key (.boundary ⟨crossing, .left⟩)).mp
          members.1
      have boundaryMem :
          (CrossingBoundary.mk crossing .left) ∈
            retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at firstData
        simpa using firstData.1
      have crossingMem :=
        retainedCrossingBoundary_crossing_mem graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈ retainedCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ retainedCompleteCarrierNodes graph key := by
        apply (mem_retainedCompleteCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold retainedDrawingCarrierNodes
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
        retainedCompleteCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1
      have siblingLeSecond :
          sibling.orderCoordinate graph ≤
            second.orderCoordinate graph := by
        rw [siblingCoordinate]
        exact gap
      have siblingEqual :=
        eq_second_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
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
        (mem_retainedCompleteCarrierNodes_iff
          graph key (.boundary ⟨crossing, .top⟩)).mp
          members.1
      have boundaryMem :
          (CrossingBoundary.mk crossing .top) ∈
            retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at firstData
        simpa using firstData.1
      have crossingMem :=
        retainedCrossingBoundary_crossing_mem graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈ retainedCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ retainedCompleteCarrierNodes graph key := by
        apply (mem_retainedCompleteCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold retainedDrawingCarrierNodes
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
        retainedCompleteCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1
      have siblingLeSecond :
          sibling.orderCoordinate graph ≤
            second.orderCoordinate graph := by
        rw [siblingCoordinate]
        exact gap
      have siblingEqual :=
        eq_second_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLtSibling siblingLeSecond
      have siblingEqual' : sibling = second := by
        simpa using siblingEqual
      subst second
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData

/-- The same forward-side classification for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_first_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (firstEqual : link.first = .boundary boundary) :
    boundary.side = .right ∨ boundary.side = .bottom :=
  retainedDrawingCompleteCarrierLinkRaw_first_boundary_side
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1 firstEqual

/-- A raw retained carrier link whose second endpoint is a crossover boundary
enters through the left or top side. -/
theorem retainedDrawingCompleteCarrierLinkRaw_second_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
        (mem_retainedCompleteCarrierNodes_iff
          graph key (.boundary ⟨crossing, .right⟩)).mp
          members.2
      have boundaryMem :
          (CrossingBoundary.mk crossing .right) ∈
            retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at secondData
        simpa using secondData.1
      have crossingMem :=
        retainedCrossingBoundary_crossing_mem graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈ retainedCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ retainedCompleteCarrierNodes graph key := by
        apply (mem_retainedCompleteCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold retainedDrawingCarrierNodes
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
        retainedCompleteCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1
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
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
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
        (mem_retainedCompleteCarrierNodes_iff
          graph key (.boundary ⟨crossing, .bottom⟩)).mp
          members.2
      have boundaryMem :
          (CrossingBoundary.mk crossing .bottom) ∈
            retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at secondData
        simpa using secondData.1
      have crossingMem :=
        retainedCrossingBoundary_crossing_mem graph boundaryMem
      have siblingBoundaryMem :
          siblingBoundary ∈ retainedCrossingBoundaries graph := by
        apply List.mem_flatMap.mpr
        refine ⟨crossing, crossingMem, ?_⟩
        simp [siblingBoundary]
      have siblingMem :
          sibling ∈ retainedCompleteCarrierNodes graph key := by
        apply (mem_retainedCompleteCarrierNodes_iff
          graph key sibling).mpr
        constructor
        · unfold retainedDrawingCarrierNodes
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
        retainedCompleteCarrierPair_orderCoordinate_add_ten_le
          wellFormed degree isLocal key pairData.1
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
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal key)
          pairData.1 siblingMem firstLeSibling siblingLtSecond
      have siblingEqual' : sibling = first := by
        simpa using siblingEqual
      subst first
      simp [sibling, siblingBoundary,
        CarrierNode.sameCrossoverSite] at pairData

/-- The same backward-side classification for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_second_boundary_side
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {boundary : CrossingBoundary}
    (secondEqual : link.second = .boundary boundary) :
    boundary.side = .left ∨ boundary.side = .top :=
  retainedDrawingCompleteCarrierLinkRaw_second_boundary_side
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1 secondEqual

/-- A terminal is the strict lower or upper extreme of every retained node
on the same physical occurrence. -/
theorem retainedCarrierNode_terminal_extreme
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {other : CarrierNode}
    (otherMem : other ∈ retainedDrawingCarrierNodes graph)
    (keyEq : other.carrierKey = terminal.carrierKey)
    (different : other ≠ CarrierNode.terminal terminal) :
    if terminal.IsLower then
      (CarrierNode.terminal terminal).orderCoordinate graph <
        other.orderCoordinate graph
    else
      other.orderCoordinate graph <
        (CarrierNode.terminal terminal).orderCoordinate graph := by
  have aligned :
      terminal.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      terminal.indexed
      (drawingSegmentTerminal_indexed_mem graph terminalMem).1
  cases other with
  | terminal otherTerminal =>
      have otherTerminalMem :
          otherTerminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at otherMem
        simpa using otherMem
      exact terminal_terminal_orderCoordinate_extreme
        graph terminalMem otherTerminalMem
        keyEq different aligned
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at otherMem
        simpa using otherMem
      exact retainedTerminal_boundary_orderCoordinate_extreme
        graph terminalMem boundaryMem keyEq aligned

/-- A terminal incident to a retained chain link occurs on the side dictated
by whether it is the lower or upper segment endpoint. -/
theorem retainedCompleteCarrierLink_terminal_orientation
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedCompleteCarrierLinks graph terminal.carrierKey)
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    if terminal.IsLower then
      link.first = .terminal terminal
    else
      link.second = .terminal terminal := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have rawPairMem :=
    (List.mem_filter.mp pairMem).1
  have members :=
    mem_of_mem_consecutivePairs rawPairMem
  have pairNe :=
    consecutivePairs_ne_of_nodup
      (retainedCompleteCarrierNodes_nodup
        graph terminal.carrierKey)
      rawPairMem
  have ordered :=
    consecutivePairs_rel_of_pairwise
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal terminal.carrierKey)
      rawPairMem
  simp only [carrierNodePairLink] at incident ⊢
  by_cases lower : terminal.IsLower
  · rw [if_pos lower]
    rcases incident with firstEq | secondEq
    · exact firstEq
    · have firstData :=
        (mem_retainedCompleteCarrierNodes_iff
          graph terminal.carrierKey pair.1).mp members.1
      have firstDifferent :
          pair.1 ≠ .terminal terminal := by
        intro firstEq
        exact pairNe (firstEq.trans secondEq.symm)
      have extreme :=
        retainedCarrierNode_terminal_extreme
          wellFormed degree isLocal terminalMem
            firstData.1 firstData.2 firstDifferent
      rw [if_pos lower] at extreme
      rw [secondEq] at ordered
      omega
  · rw [if_neg lower]
    rcases incident with firstEq | secondEq
    · have secondData :=
        (mem_retainedCompleteCarrierNodes_iff
          graph terminal.carrierKey pair.2).mp members.2
      have secondDifferent :
          pair.2 ≠ .terminal terminal := by
        intro secondEq
        exact pairNe (firstEq.trans secondEq.symm)
      have extreme :=
        retainedCarrierNode_terminal_extreme
          wellFormed degree isLocal terminalMem
            secondData.1 secondData.2 secondDifferent
      rw [if_neg lower] at extreme
      rw [firstEq] at ordered
      omega
    · exact secondEq

/-- A selected retained link incident to a terminal has the corresponding
lower/upper endpoint orientation. -/
theorem retainedDrawingCompleteCarrierLink_terminal_orientation
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    if terminal.IsLower then
      link.first = .terminal terminal
    else
      link.second = .terminal terminal := by
  have rawMem :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1
  rcases List.mem_flatMap.mp rawMem with
    ⟨key, _keyMem, chainMem⟩
  have common :=
    retainedCompleteCarrierLinks_common_key graph key chainMem
  have keyEq : key = terminal.carrierKey := by
    rcases incident with incident | incident
    · simpa [incident, CarrierNode.carrierKey] using common.1.symm
    · simpa [incident, CarrierNode.carrierKey] using common.2.symm
  apply retainedCompleteCarrierLink_terminal_orientation
    wellFormed degree isLocal terminalMem
  · simpa [keyEq] using chainMem
  · exact incident

end PeriodicOrthocrossing
end LeanTrominoes
