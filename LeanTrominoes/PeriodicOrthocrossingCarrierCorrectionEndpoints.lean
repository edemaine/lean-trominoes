import LeanTrominoes.PeriodicOrthocrossingRetainedBoundaryGeometry

/-!
# Retained endpoints after carrier representative correction

The owner correction sends the selected endpoint to a canonical boundary (or
a zero-translation terminal).  Because both endpoints remain on one physical
carrier, the other endpoint then uses the same neighboring segment occurrence.
The retained-crossing shift bound shows that a boundary endpoint remains in
the `5 × 5` orbit window; terminal endpoints remain among the enumerated
neighboring occurrence terminals.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A terminal is enumerated whenever its indexed segment is listed and its
occurrence translation is neighboring. -/
theorem mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (indexedMem :
      terminal.indexed ∈ (drawing graph).indexedSegments)
    (translateNeighbor :
      IsNeighborTranslation terminal.translate) :
    terminal ∈ drawingSegmentTerminals graph := by
  apply List.mem_flatMap.mpr
  refine
    ⟨(terminal.indexed, terminal.translate),
      (mem_neighborOccurrences_iff graph _).mpr
        ⟨indexedMem, translateNeighbor⟩, ?_⟩
  cases terminal with
  | mk indexed translate endpoint =>
      cases endpoint <;> simp [occurrenceTerminals]

/-- Period translation preserves the indexed segment projected from a carrier
node. -/
@[simp]
theorem CarrierNode.indexed_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).indexed = node.indexed := by
  cases node with
  | boundary boundary =>
      exact CrossingBoundary.indexed_periodTranslate graph boundary shift
  | terminal terminal =>
      rfl

/-- Period translation adds the common shift to a carrier node's occurrence
translation. -/
@[simp]
theorem CarrierNode.translate_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).translate =
      Cell.add node.translate shift := by
  cases node with
  | boundary boundary =>
      exact CrossingBoundary.translate_periodTranslate graph boundary shift
  | terminal terminal =>
      rfl

/-- Equal carrier keys recover indexed-segment and translation equality when
both indexed segments are known to be listed. -/
theorem carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CarrierNode}
    (firstIndexed :
      first.indexed ∈ (drawing graph).indexedSegments)
    (secondIndexed :
      second.indexed ∈ (drawing graph).indexedSegments)
    (keyEq : first.carrierKey = second.carrierKey) :
    first.indexed = second.indexed ∧
      first.translate = second.translate := by
  rw [CarrierNode.carrierKey_eq_indexed_translate,
    CarrierNode.carrierKey_eq_indexed_translate] at keyEq
  have routeEq :
      first.indexed.routeIndex = second.indexed.routeIndex :=
    congrArg Prod.fst keyEq
  have segmentEq :
      first.indexed.segmentIndex = second.indexed.segmentIndex :=
    congrArg (fun key => key.2.1) keyEq
  have indexedEq :=
    indexedSegment_eq_of_indices_eq (drawing graph)
      firstIndexed secondIndexed routeEq segmentEq
  exact ⟨indexedEq,
    congrArg (fun key => key.2.2) keyEq⟩

/-- Every retained carrier node projects to a listed indexed segment. -/
theorem retainedCarrierNode_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph) :
    node.indexed ∈ (drawing graph).indexedSegments := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact
        (retainedCrossingBoundary_indexed_mem_and_contains
          graph boundaryMem).1
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact (drawingSegmentTerminal_indexed_mem graph terminalMem).1

/-- Translating a retained node preserves listed indexed-segment membership. -/
theorem retainedCarrierNode_periodTranslate_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (shift : Cell) :
    (node.periodTranslate graph shift).indexed ∈
      (drawing graph).indexedSegments := by
  simpa using retainedCarrierNode_indexed_mem graph nodeMem

/-- Common translation preserves the fact that the two endpoints of a link
use one physical carrier key. -/
theorem carrierLinkPeriodTranslate_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell)
    (common : link.first.carrierKey = link.second.carrierKey) :
    (carrierLinkPeriodTranslate graph link shift).first.carrierKey =
      (carrierLinkPeriodTranslate graph link shift).second.carrierKey := by
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.carrierKey_periodTranslate]
  rw [common]

/-- A translated retained boundary whose carrier key agrees with a canonical
boundary remains inside the bounded retained crossing orbit. -/
theorem retainedCrossingBoundary_periodTranslate_mem_of_carrierKey_eq_canonical
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {boundary canonical : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph)
    (canonicalMem :
      canonical ∈ drawingCrossingBoundaries graph)
    (shift : Cell)
    (keyEq :
      (boundary.periodTranslate graph shift).carrierKey =
        canonical.carrierKey) :
    boundary.periodTranslate graph shift ∈
      retainedCrossingBoundaries graph := by
  let translated := boundary.periodTranslate graph shift
  have translatedData :=
    retainedCrossingBoundary_periodTranslate_indexed_mem_and_contains
      graph boundaryMem shift
  have canonicalData :=
    drawingCrossingBoundary_indexed_mem_and_translate_neighbor
      graph canonicalMem
  have fields :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (first := .boundary translated)
      (second := .boundary canonical)
      translatedData.1 canonicalData.1
      (by
        simpa [CarrierNode.carrierKey, translated] using keyEq)
  have translatedNeighbor :
      IsNeighborTranslation translated.translate := by
    change
      IsNeighborTranslation
        (CarrierNode.boundary translated).translate
    rw [fields.2]
    exact canonicalData.2
  have pointBounds :
      InCarrierCrossingRetentionSquare graph
        translated.crossing.point :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal translatedData.1
        translatedNeighbor translatedData.2
  have shiftMem :
      crossingPeriodShift graph translated.crossing ∈
        carrierCrossingRetentionShifts :=
    crossingPeriodShift_mem_retentionShifts
      graph translated.crossing pointBounds
  have normalizedBoundaryMem :
      translated.periodNormalize graph ∈
        drawingCrossingBoundaries graph := by
    simpa [translated] using
      retainedCrossingBoundary_periodNormalize_mem
        graph boundaryMem
  have normalizedCrossingMem :
      translated.crossing.periodNormalize graph ∈
        orientedCrossings graph :=
    drawingCrossingBoundary_crossing_mem_orientedCrossings
      graph normalizedBoundaryMem
  have crossingMem :
      translated.crossing ∈ retainedCrossings graph :=
    mem_retainedCrossings_of_periodNormalize_mem_of_shift_mem
      graph translated.crossing normalizedCrossingMem shiftMem
  change translated ∈ retainedCrossingBoundaries graph
  rcases translated with ⟨crossing, side⟩
  apply List.mem_flatMap.mpr
  refine ⟨crossing, crossingMem, ?_⟩
  cases side <;> simp

/-- A translated retained terminal whose key agrees with a canonical
boundary remains an enumerated neighboring terminal. -/
theorem retainedTerminal_periodTranslate_mem_of_carrierKey_eq_canonical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem :
      terminal ∈ drawingSegmentTerminals graph)
    {canonical : CrossingBoundary}
    (canonicalMem :
      canonical ∈ drawingCrossingBoundaries graph)
    (shift : Cell)
    (keyEq :
      (CarrierNode.terminal (terminal.periodTranslate shift)).carrierKey =
        (CarrierNode.boundary canonical).carrierKey) :
    terminal.periodTranslate shift ∈
      drawingSegmentTerminals graph := by
  have terminalIndexed :
      (CarrierNode.terminal
        (terminal.periodTranslate shift)).indexed ∈
          (drawing graph).indexedSegments := by
    change
      (terminal.periodTranslate shift).indexed ∈
        (drawing graph).indexedSegments
    simpa [SegmentTerminal.periodTranslate] using
      (drawingSegmentTerminal_indexed_mem
        graph terminalMem).1
  have canonicalData :=
    drawingCrossingBoundary_indexed_mem_and_translate_neighbor
      graph canonicalMem
  have fields :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (first := .terminal (terminal.periodTranslate shift))
      (second := .boundary canonical)
      terminalIndexed canonicalData.1 keyEq
  apply mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
    graph (terminal.periodTranslate shift)
  · exact terminalIndexed
  · rw [show (terminal.periodTranslate shift).translate =
        (CarrierNode.terminal
          (terminal.periodTranslate shift)).translate by rfl,
      fields.2]
    exact canonicalData.2

/-- Correcting any raw retained link leaves both endpoints in the retained
carrier-node enumeration. -/
theorem carrierLinkRepresentativeCorrection_endpoints_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    let corrected :=
      carrierLinkPeriodTranslate graph link
        (carrierLinkRepresentativeCorrection graph link)
    corrected.first ∈ retainedDrawingCarrierNodes graph ∧
      corrected.second ∈ retainedDrawingCarrierNodes graph := by
  let correction :=
    carrierLinkRepresentativeCorrection graph link
  let corrected :=
    carrierLinkPeriodTranslate graph link correction
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have common :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have correctedCommon :
      corrected.first.carrierKey =
        corrected.second.carrierKey :=
    carrierLinkPeriodTranslate_common_key
      graph link correction common
  cases firstEq : link.first with
  | boundary firstBoundary =>
      have firstBoundaryMem :
          firstBoundary ∈ retainedCrossingBoundaries graph := by
        rw [firstEq] at endpoints
        unfold retainedDrawingCarrierNodes at endpoints
        simpa using endpoints.1
      have canonicalFirstMem :
          firstBoundary.periodNormalize graph ∈
            drawingCrossingBoundaries graph :=
        retainedCrossingBoundary_periodNormalize_mem
          graph firstBoundaryMem
      have correctedFirstEq :
          corrected.first =
            .boundary (firstBoundary.periodNormalize graph) := by
        exact carrierLinkRepresentativeCorrection_first_boundary
          graph firstEq
      have correctedFirstMem :
          corrected.first ∈ retainedDrawingCarrierNodes graph := by
        rw [correctedFirstEq]
        unfold retainedDrawingCarrierNodes
        simp
        exact
          drawingCrossingBoundaries_subset_retainedCrossingBoundaries
            graph canonicalFirstMem
      cases secondEq : link.second with
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            rw [secondEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.2
          have correctedSecondBoundaryMem :
              secondBoundary.periodTranslate graph correction ∈
                retainedCrossingBoundaries graph := by
            apply
              retainedCrossingBoundary_periodTranslate_mem_of_carrierKey_eq_canonical
                wellFormed degree isLocal secondBoundaryMem
                  canonicalFirstMem correction
            have correctedSecondEq :
                corrected.second =
                  .boundary
                    (secondBoundary.periodTranslate graph correction) := by
              simp [corrected, secondEq,
                CarrierNode.periodTranslate]
            rw [correctedFirstEq, correctedSecondEq] at correctedCommon
            exact correctedCommon.symm
          refine ⟨correctedFirstMem, ?_⟩
          rw [show corrected.second =
              .boundary
                (secondBoundary.periodTranslate graph correction) by
            simp [corrected, secondEq,
              CarrierNode.periodTranslate]]
          unfold retainedDrawingCarrierNodes
          simp [correctedSecondBoundaryMem]
      | terminal secondTerminal =>
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            rw [secondEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.2
          have correctedSecondTerminalMem :
              secondTerminal.periodTranslate correction ∈
                drawingSegmentTerminals graph := by
            apply
              retainedTerminal_periodTranslate_mem_of_carrierKey_eq_canonical
                graph secondTerminalMem canonicalFirstMem correction
            have correctedSecondEq :
                corrected.second =
                  .terminal
                    (secondTerminal.periodTranslate correction) := by
              simp [corrected, secondEq,
                CarrierNode.periodTranslate]
            rw [correctedFirstEq, correctedSecondEq] at correctedCommon
            exact correctedCommon.symm
          refine ⟨correctedFirstMem, ?_⟩
          rw [show corrected.second =
              .terminal
                (secondTerminal.periodTranslate correction) by
            simp [corrected, secondEq,
              CarrierNode.periodTranslate]]
          unfold retainedDrawingCarrierNodes
          simp [correctedSecondTerminalMem]
  | terminal firstTerminal =>
      cases secondEq : link.second with
      | boundary secondBoundary =>
          have firstTerminalMem :
              firstTerminal ∈ drawingSegmentTerminals graph := by
            rw [firstEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.1
          have secondBoundaryMem :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            rw [secondEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.2
          have canonicalSecondMem :
              secondBoundary.periodNormalize graph ∈
                drawingCrossingBoundaries graph :=
            retainedCrossingBoundary_periodNormalize_mem
              graph secondBoundaryMem
          have correctedSecondEq :
              corrected.second =
                .boundary
                  (secondBoundary.periodNormalize graph) := by
            exact
              carrierLinkRepresentativeCorrection_terminal_boundary
                graph firstEq secondEq
          have correctedFirstTerminalMem :
              firstTerminal.periodTranslate correction ∈
                drawingSegmentTerminals graph := by
            apply
              retainedTerminal_periodTranslate_mem_of_carrierKey_eq_canonical
                graph firstTerminalMem canonicalSecondMem correction
            have correctedFirstNodeEq :
                corrected.first =
                  .terminal
                    (firstTerminal.periodTranslate correction) := by
              simp [corrected, firstEq,
                CarrierNode.periodTranslate]
            rw [correctedFirstNodeEq, correctedSecondEq] at correctedCommon
            exact correctedCommon
          constructor
          · rw [show corrected.first =
                .terminal
                  (firstTerminal.periodTranslate correction) by
              simp [corrected, firstEq,
                CarrierNode.periodTranslate]]
            unfold retainedDrawingCarrierNodes
            simp [correctedFirstTerminalMem]
          · rw [correctedSecondEq]
            unfold retainedDrawingCarrierNodes
            simp
            exact
              drawingCrossingBoundaries_subset_retainedCrossingBoundaries
                graph canonicalSecondMem
      | terminal secondTerminal =>
          have firstTerminalMem :
              firstTerminal ∈ drawingSegmentTerminals graph := by
            rw [firstEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.1
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            rw [secondEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.2
          have correctedFirstEq :
              corrected.first =
                .terminal
                  ⟨firstTerminal.indexed, (0, 0),
                    firstTerminal.endpoint⟩ :=
            carrierLinkRepresentativeCorrection_terminal_terminal
              graph firstEq secondEq
          let firstCorrectedTerminal : SegmentTerminal :=
            ⟨firstTerminal.indexed, (0, 0),
              firstTerminal.endpoint⟩
          have firstCorrectedIndexed :
              (CarrierNode.terminal firstCorrectedTerminal).indexed ∈
                (drawing graph).indexedSegments := by
            change firstCorrectedTerminal.indexed ∈
              (drawing graph).indexedSegments
            simpa [firstCorrectedTerminal] using
              (drawingSegmentTerminal_indexed_mem
                graph firstTerminalMem).1
          have secondCorrectedIndexed :
              (CarrierNode.terminal
                (secondTerminal.periodTranslate correction)).indexed ∈
                  (drawing graph).indexedSegments := by
            change (secondTerminal.periodTranslate correction).indexed ∈
              (drawing graph).indexedSegments
            simpa [SegmentTerminal.periodTranslate] using
              (drawingSegmentTerminal_indexed_mem
                graph secondTerminalMem).1
          have fields :=
            carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
              graph firstCorrectedIndexed secondCorrectedIndexed
                (by
                  have correctedSecondEq :
                      corrected.second =
                        .terminal
                          (secondTerminal.periodTranslate correction) := by
                    simp [corrected, secondEq,
                      CarrierNode.periodTranslate]
                  rw [correctedFirstEq, correctedSecondEq] at correctedCommon
                  simpa [firstCorrectedTerminal] using correctedCommon)
          have firstCorrectedMem :
              firstCorrectedTerminal ∈
                drawingSegmentTerminals graph := by
            apply
              mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
                graph firstCorrectedTerminal firstCorrectedIndexed
            simp [firstCorrectedTerminal, IsNeighborTranslation]
          have secondCorrectedMem :
              secondTerminal.periodTranslate correction ∈
                drawingSegmentTerminals graph := by
            apply
              mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
                graph (secondTerminal.periodTranslate correction)
                  secondCorrectedIndexed
            have translateEq :
                firstCorrectedTerminal.translate =
                  (secondTerminal.periodTranslate correction).translate := by
              simpa [CarrierNode.translate] using fields.2
            rw [← translateEq]
            simp [firstCorrectedTerminal, IsNeighborTranslation]
          constructor
          · rw [correctedFirstEq]
            unfold retainedDrawingCarrierNodes
            simp [firstCorrectedTerminal, firstCorrectedMem]
          · rw [show corrected.second =
                .terminal
                  (secondTerminal.periodTranslate correction) by
              simp [corrected, secondEq,
                CarrierNode.periodTranslate]]
            unfold retainedDrawingCarrierNodes
            simp [secondCorrectedMem]

end PeriodicOrthocrossing
end LeanTrominoes
