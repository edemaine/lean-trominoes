import LeanTrominoes.PeriodicOrthocrossingCrossingTranslationDegree
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-!
# Terminal degree in complete segment carriers

Terminals are the two endpoint variables added to every neighboring segment
occurrence.  This file proves geometrically that each terminal is a strict
extreme of the complete carrier chain obtained by sorting the terminals and
crossover boundaries along that segment.  Consequently a terminal is
incident to at most one retained consecutive-pair equality link.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

theorem indexedSegment_eq_of_indices_eq
    (drawing : PeriodicGridDrawing)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ drawing.indexedSegments)
    (secondMem : second ∈ drawing.indexedSegments)
    (routeEq : first.routeIndex = second.routeIndex)
    (segmentEq : first.segmentIndex = second.segmentIndex) :
    first = second := by
  unfold PeriodicGridDrawing.indexedSegments at firstMem secondMem
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstRoute, firstRouteMem, firstMem⟩
  rcases List.mem_map.mp firstMem with
    ⟨firstSegment, firstSegmentMem, firstEq⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondRoute, secondRouteMem, secondMem⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondSegment, secondSegmentMem, secondEq⟩
  subst first
  subst second
  have routesEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstRouteMem secondRouteMem routeEq
  subst secondRoute
  have segmentsEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstSegmentMem secondSegmentMem segmentEq
  subst secondSegment
  rfl

theorem drawingSegmentTerminal_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph) :
    terminal.indexed ∈ (drawing graph).indexedSegments ∧
      IsNeighborTranslation terminal.translate := by
  rcases List.mem_flatMap.mp terminalMem with
    ⟨occurrence, occurrenceMem, terminalMem⟩
  have occurrenceData :=
    (mem_neighborOccurrences_iff graph occurrence).mp occurrenceMem
  simp only [occurrenceTerminals, List.mem_cons,
    List.not_mem_nil, or_false] at terminalMem
  rcases terminalMem with terminalEq | terminalEq <;>
    subst terminal <;> exact occurrenceData

theorem segmentTerminals_indexed_translate_eq_of_carrierKey_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : SegmentTerminal}
    (firstMem : first ∈ drawingSegmentTerminals graph)
    (secondMem : second ∈ drawingSegmentTerminals graph)
    (keyEq : first.carrierKey = second.carrierKey) :
    first.indexed = second.indexed ∧
      first.translate = second.translate := by
  have firstData :=
    drawingSegmentTerminal_indexed_mem graph firstMem
  have secondData :=
    drawingSegmentTerminal_indexed_mem graph secondMem
  have routeEq :
      first.indexed.routeIndex = second.indexed.routeIndex := by
    exact congrArg Prod.fst keyEq
  have segmentEq :
      first.indexed.segmentIndex = second.indexed.segmentIndex := by
    exact congrArg (fun key => key.2.1) keyEq
  have indexedEq :=
    indexedSegment_eq_of_indices_eq (drawing graph)
      firstData.1 secondData.1 routeEq segmentEq
  refine ⟨indexedEq, ?_⟩
  exact congrArg (fun key => key.2.2) keyEq

theorem crossingBoundary_terminal_indexed_translate_eq_of_carrierKey_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    (keyEq : boundary.carrierKey = terminal.carrierKey) :
    boundary.indexed = terminal.indexed ∧
      boundary.translate = terminal.translate := by
  have boundaryData :=
    drawingCrossingBoundary_indexed_mem_and_translate_mem
      graph boundaryMem
  have terminalData :=
    drawingSegmentTerminal_indexed_mem graph terminalMem
  rw [CrossingBoundary.carrierKey_eq_indexed_translate] at keyEq
  have routeEq :
      boundary.indexed.routeIndex = terminal.indexed.routeIndex := by
    exact congrArg Prod.fst keyEq
  have segmentEq :
      boundary.indexed.segmentIndex = terminal.indexed.segmentIndex := by
    exact congrArg (fun key => key.2.1) keyEq
  have indexedEq :=
    indexedSegment_eq_of_indices_eq (drawing graph)
      boundaryData.1 terminalData.1 routeEq segmentEq
  refine ⟨indexedEq, ?_⟩
  exact congrArg (fun key => key.2.2) keyEq

theorem drawingCrossingBoundary_point_data
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph) :
    InFundamentalDrawingSquare graph boundary.crossing.point ∧
      (boundary.indexed.segment.translate
        ((drawing graph).periodTranslation boundary.translate)).InteriorContains
          boundary.crossing.point := by
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, boundaryMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at boundaryMem
  have sound := orientedCrossings_sound graph crossingMem
  have canonical := sound.2.2.2.2.1
  rcases boundaryMem with
    boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
      subst boundary
  · exact ⟨canonical.1, canonical.2.2.1⟩
  · exact ⟨canonical.1, canonical.2.2.1⟩
  · exact ⟨canonical.1, canonical.2.2.2.1⟩
  · exact ⟨canonical.1, canonical.2.2.2.1⟩

theorem drawingCrossingBoundary_crossing_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph) :
    boundary.crossing ∈ orientedCrossings graph := by
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, boundaryMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at boundaryMem
  rcases boundaryMem with
    boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
      subst boundary <;> exact crossingMem

theorem carrierNode_terminal_orderCoordinate_horizontal
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (horizontal : terminal.indexed.segment.IsHorizontal) :
    (CarrierNode.terminal terminal).orderCoordinate graph =
      (terminal.position graph).1 := by
  simp [CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
    CarrierNode.position,
    horizontal]

theorem carrierNode_terminal_orderCoordinate_vertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (vertical : terminal.indexed.segment.IsVertical) :
    (CarrierNode.terminal terminal).orderCoordinate graph =
      (terminal.position graph).2 := by
  have notHorizontal :
      ¬terminal.indexed.segment.IsHorizontal := by
    intro horizontal
    exact vertical.2 horizontal.1
  simp [CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
    CarrierNode.position,
    notHorizontal]

theorem carrierNode_boundary_orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) :
    (CarrierNode.boundary boundary).orderCoordinate graph =
      match boundary.side with
      | .left | .right => (boundary.position).1
      | .top | .bottom => (boundary.position).2 := by
  cases boundary with
  | mk crossing side =>
      cases side <;>
        rfl

/-- Whether a terminal is the endpoint with smaller coordinate along its
axis-aligned segment. -/
def SegmentTerminal.IsLower (terminal : SegmentTerminal) : Prop :=
  match terminal.endpoint with
  | .start =>
      terminal.indexed.segment.start.1 <
          terminal.indexed.segment.finish.1 ∨
        terminal.indexed.segment.start.2 <
          terminal.indexed.segment.finish.2
  | .finish =>
      terminal.indexed.segment.finish.1 <
          terminal.indexed.segment.start.1 ∨
        terminal.indexed.segment.finish.2 <
          terminal.indexed.segment.start.2

instance (terminal : SegmentTerminal) :
    Decidable terminal.IsLower := by
  unfold SegmentTerminal.IsLower
  split <;> infer_instance

theorem terminal_boundary_orderCoordinate_extreme
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph)
    (keyEq : boundary.carrierKey = terminal.carrierKey)
    (axisAligned : terminal.indexed.segment.IsAxisAligned) :
    if terminal.IsLower then
      (CarrierNode.terminal terminal).orderCoordinate graph <
        (CarrierNode.boundary boundary).orderCoordinate graph
    else
      (CarrierNode.boundary boundary).orderCoordinate graph <
        (CarrierNode.terminal terminal).orderCoordinate graph := by
  have carrierData :=
    crossingBoundary_terminal_indexed_translate_eq_of_carrierKey_eq
      graph boundaryMem terminalMem keyEq
  have pointData :=
    drawingCrossingBoundary_point_data graph boundaryMem
  have crossingMem :=
    drawingCrossingBoundary_crossing_mem graph boundaryMem
  have sound := orientedCrossings_sound graph crossingMem
  rcases axisAligned with horizontal | vertical
  · rw [carrierNode_terminal_orderCoordinate_horizontal
      graph terminal horizontal]
    rw [carrierNode_boundary_orderCoordinate]
    cases boundary with
    | mk crossing side =>
        cases side
        · simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne horizontal.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, horizontal.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne horizontal.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, horizontal.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CrossingBoundary.indexed] at carrierData
          have crossingVertical :
              crossing.second.segment.IsVertical :=
            (GridSegment.isVertical_translate _ _).mp
              sound.2.2.2.2.2.2
          rw [carrierData.1] at crossingVertical
          exact (crossingVertical.2 horizontal.1).elim
        · simp only [CrossingBoundary.indexed] at carrierData
          have crossingVertical :
              crossing.second.segment.IsVertical :=
            (GridSegment.isVertical_translate _ _).mp
              sound.2.2.2.2.2.2
          rw [carrierData.1] at crossingVertical
          exact (crossingVertical.2 horizontal.1).elim
  · rw [carrierNode_terminal_orderCoordinate_vertical
      graph terminal vertical]
    rw [carrierNode_boundary_orderCoordinate]
    cases boundary with
    | mk crossing side =>
        cases side
        · simp only [CrossingBoundary.indexed] at carrierData
          have crossingHorizontal :
              crossing.first.segment.IsHorizontal :=
            (GridSegment.isHorizontal_translate _ _).mp
              sound.2.2.2.2.2.1
          rw [carrierData.1] at crossingHorizontal
          exact (vertical.2 crossingHorizontal.1).elim
        · simp only [CrossingBoundary.indexed] at carrierData
          have crossingHorizontal :
              crossing.first.segment.IsHorizontal :=
            (GridSegment.isHorizontal_translate _ _).mp
              sound.2.2.2.2.2.1
          rw [carrierData.1] at crossingHorizontal
          exact (vertical.2 crossingHorizontal.1).elim
        · simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne vertical.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, vertical.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne vertical.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, vertical.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega

theorem terminal_terminal_orderCoordinate_extreme
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal other : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    (otherMem : other ∈ drawingSegmentTerminals graph)
    (keyEq : other.carrierKey = terminal.carrierKey)
    (different :
      CarrierNode.terminal other ≠ CarrierNode.terminal terminal)
    (axisAligned : terminal.indexed.segment.IsAxisAligned) :
    if terminal.IsLower then
      (CarrierNode.terminal terminal).orderCoordinate graph <
        (CarrierNode.terminal other).orderCoordinate graph
    else
      (CarrierNode.terminal other).orderCoordinate graph <
        (CarrierNode.terminal terminal).orderCoordinate graph := by
  have carrierData :=
    segmentTerminals_indexed_translate_eq_of_carrierKey_eq
      graph otherMem terminalMem keyEq
  have equal_of_endpoint_eq
      (endpointEq : other.endpoint = terminal.endpoint) :
      other = terminal := by
    cases terminal
    cases other
    simp_all
  have endpointNe : other.endpoint ≠ terminal.endpoint := by
    intro endpointEq
    exact different
      (congrArg CarrierNode.terminal
        (equal_of_endpoint_eq endpointEq))
  rcases axisAligned with horizontal | vertical
  · generalize terminalEndpointEq :
      terminal.endpoint = terminalEndpoint
    generalize otherEndpointEq :
      other.endpoint = otherEndpoint
    cases terminalEndpoint <;> cases otherEndpoint <;>
      simp_all [SegmentTerminal.IsLower,
        GridSegment.IsHorizontal,
        CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
        CarrierNode.position, SegmentTerminal.position,
        SegmentTerminal.drawingPoint,
        segmentTerminalLocalPosition, GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        planarMacroScale, Cell.add, Cell.scale] <;>
      (try split_ifs) <;> simp_all <;> omega
  · have notHorizontal :
        ¬terminal.indexed.segment.IsHorizontal := by
      intro horizontal
      exact vertical.2 horizontal.1
    generalize terminalEndpointEq :
      terminal.endpoint = terminalEndpoint
    generalize otherEndpointEq :
      other.endpoint = otherEndpoint
    cases terminalEndpoint <;> cases otherEndpoint <;>
      simp_all [SegmentTerminal.IsLower,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
        CarrierNode.position, SegmentTerminal.position,
        SegmentTerminal.drawingPoint,
        segmentTerminalLocalPosition, GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        planarMacroScale, Cell.add, Cell.scale] <;>
      (try split_ifs) <;> simp_all <;> omega

/-- A terminal is a strict extreme of every other node on its translated
segment occurrence. -/
theorem carrierNode_terminal_extreme
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph)
    (keyEq : node.carrierKey = terminal.carrierKey)
    (different : node ≠ CarrierNode.terminal terminal) :
    if terminal.IsLower then
      (CarrierNode.terminal terminal).orderCoordinate graph <
        node.orderCoordinate graph
    else
      node.orderCoordinate graph <
        (CarrierNode.terminal terminal).orderCoordinate graph := by
  have terminalData :=
    drawingSegmentTerminal_indexed_mem graph terminalMem
  have axisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      terminal.indexed terminalData.1
  rcases List.mem_append.mp nodeMem with terminalNodeMem | boundaryNodeMem
  · rcases List.mem_map.mp terminalNodeMem with
      ⟨other, otherMem, nodeEq⟩
    subst node
    exact terminal_terminal_orderCoordinate_extreme
      graph terminalMem otherMem keyEq different axisAligned
  · rcases List.mem_map.mp boundaryNodeMem with
      ⟨boundary, boundaryMem, nodeEq⟩
    subst node
    exact terminal_boundary_orderCoordinate_extreme
      graph terminalMem boundaryMem keyEq axisAligned

/-- Adjacent pairs inherit their relation from a pairwise-related list. -/
theorem consecutivePairs_rel_of_pairwise
    {Value : Type*} {relation : Value → Value → Prop}
    {values : List Value} (pairwise : values.Pairwise relation)
    {pair : Value × Value}
    (pairMem : pair ∈ consecutivePairs values) :
    relation pair.1 pair.2 := by
  induction values with
  | nil =>
      simp [consecutivePairs] at pairMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [consecutivePairs] at pairMem
      | cons second rest =>
          rw [List.pairwise_cons] at pairwise
          simp only [consecutivePairs, List.mem_cons] at pairMem
          rcases pairMem with pairEq | pairMem
          · subst pair
            exact pairwise.1 second (by simp)
          · exact induction pairwise.2 pairMem

/-- Adjacent elements of a noduplicated list are distinct. -/
theorem consecutivePairs_ne_of_nodup
    {Value : Type*} [DecidableEq Value]
    {values : List Value} (nodup : values.Nodup)
    {pair : Value × Value}
    (pairMem : pair ∈ consecutivePairs values) :
    pair.1 ≠ pair.2 := by
  intro equal
  induction values with
  | nil =>
      simp [consecutivePairs] at pairMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [consecutivePairs] at pairMem
      | cons second rest =>
          rw [List.nodup_cons] at nodup
          simp only [consecutivePairs, List.mem_cons] at pairMem
          rcases pairMem with pairEq | pairMem
          · subst pair
            have equal' : first = second := by
              simpa using equal
            exact nodup.1 (by simp [equal'])
          · exact induction nodup.2 pairMem

/-- If a value cannot be a second endpoint, a subfamily of adjacent pairs
in a simple list is incident to it at most once. -/
theorem pairEndpoints_count_le_one_of_not_mem_snd
    {Value : Type*} [DecidableEq Value]
    {values : List Value} (valuesNodup : values.Nodup)
    {pairs : List (Value × Value)}
    (pairsSublist :
      List.Sublist pairs (consecutivePairs values))
    (value : Value)
    (notSecond : value ∉ pairs.map Prod.snd) :
    (pairEndpoints pairs).count value ≤ 1 := by
  rw [pairEndpoints_count]
  have firstSublist :
      List.Sublist (pairs.map Prod.fst) values :=
    (pairsSublist.map Prod.fst).trans
      (consecutivePairs_fst_sublist values)
  have firstLe :
      (pairs.map Prod.fst).count value ≤ 1 :=
    firstSublist.subperm.count_le value |>.trans
      ((List.nodup_iff_count_le_one.mp valuesNodup) value)
  have secondZero :
      (pairs.map Prod.snd).count value = 0 :=
    List.count_eq_zero_of_not_mem notSecond
  omega

/-- Symmetric first-endpoint form of
`pairEndpoints_count_le_one_of_not_mem_snd`. -/
theorem pairEndpoints_count_le_one_of_not_mem_fst
    {Value : Type*} [DecidableEq Value]
    {values : List Value} (valuesNodup : values.Nodup)
    {pairs : List (Value × Value)}
    (pairsSublist :
      List.Sublist pairs (consecutivePairs values))
    (value : Value)
    (notFirst : value ∉ pairs.map Prod.fst) :
    (pairEndpoints pairs).count value ≤ 1 := by
  rw [pairEndpoints_count]
  have secondSublist :
      List.Sublist (pairs.map Prod.snd) values :=
    (pairsSublist.map Prod.snd).trans
      (consecutivePairs_snd_sublist values)
  have secondLe :
      (pairs.map Prod.snd).count value ≤ 1 :=
    secondSublist.subperm.count_le value |>.trans
      ((List.nodup_iff_count_le_one.mp valuesNodup) value)
  have firstZero :
      (pairs.map Prod.fst).count value = 0 :=
    List.count_eq_zero_of_not_mem notFirst
  omega

/-- Because terminals are strict extremes of their sorted carrier chain,
each terminal is incident to at most one retained complete-carrier link. -/
theorem completeCarrierLinks_terminal_endpoint_count_le_one
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph) :
    (equalityLinkEndpoints
      (completeCarrierLinks graph terminal.carrierKey)).count
        (CarrierNode.terminal terminal) ≤ 1 := by
  rw [completeCarrierLinks_endpoints]
  let nodes :=
    completeCarrierNodes graph terminal.carrierKey
  let pairs :=
    (consecutivePairs nodes).filter fun pair =>
      !pair.1.sameCrossoverSite pair.2
  have nodesNodup : nodes.Nodup :=
    completeCarrierNodes_nodup graph terminal.carrierKey
  have pairsSublist :
      List.Sublist pairs (consecutivePairs nodes) :=
    List.filter_sublist
  have nodesSorted :
      nodes.Pairwise fun first second =>
        first.orderCoordinate graph ≤
          second.orderCoordinate graph := by
    unfold nodes completeCarrierNodes
    exact List.pairwise_insertionSort _ _
  by_cases lower : terminal.IsLower
  · apply pairEndpoints_count_le_one_of_not_mem_snd
      nodesNodup pairsSublist
    intro terminalSecond
    rcases List.mem_map.mp terminalSecond with
      ⟨pair, pairMem, secondEq⟩
    have rawPairMem :
        pair ∈ consecutivePairs nodes :=
      (List.mem_filter.mp pairMem).1
    have members :=
      mem_of_mem_consecutivePairs rawPairMem
    have pairNe :=
      consecutivePairs_ne_of_nodup nodesNodup rawPairMem
    have firstData :=
      (mem_completeCarrierNodes_iff
        graph terminal.carrierKey pair.1).mp members.1
    have firstDifferent :
        pair.1 ≠ CarrierNode.terminal terminal := by
      intro firstEq
      exact pairNe (firstEq.trans secondEq.symm)
    have extreme :=
      carrierNode_terminal_extreme
        wellFormed degree isLocal terminalMem
          firstData.1 firstData.2 firstDifferent
    rw [if_pos lower] at extreme
    have ordered :=
      consecutivePairs_rel_of_pairwise
        nodesSorted rawPairMem
    rw [secondEq] at ordered
    omega
  · apply pairEndpoints_count_le_one_of_not_mem_fst
      nodesNodup pairsSublist
    intro terminalFirst
    rcases List.mem_map.mp terminalFirst with
      ⟨pair, pairMem, firstEq⟩
    have rawPairMem :
        pair ∈ consecutivePairs nodes :=
      (List.mem_filter.mp pairMem).1
    have members :=
      mem_of_mem_consecutivePairs rawPairMem
    have pairNe :=
      consecutivePairs_ne_of_nodup nodesNodup rawPairMem
    have secondData :=
      (mem_completeCarrierNodes_iff
        graph terminal.carrierKey pair.2).mp members.2
    have secondDifferent :
        pair.2 ≠ CarrierNode.terminal terminal := by
      intro secondEq
      exact pairNe (firstEq.trans secondEq.symm)
    have extreme :=
      carrierNode_terminal_extreme
        wellFormed degree isLocal terminalMem
          secondData.1 secondData.2 secondDifferent
    rw [if_neg lower] at extreme
    have ordered :=
      consecutivePairs_rel_of_pairwise
        nodesSorted rawPairMem
    rw [firstEq] at ordered
    omega

end PeriodicOrthocrossing
end LeanTrominoes
