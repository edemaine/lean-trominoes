/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks
import LeanTrominoes.PeriodicOrthocrossingRetainedBoundaryCarrierKeyAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedSegmentTerminalIndexedSemantics

/-! # Descriptor-derived axes of retained carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A descriptor stream reconstructing the drawing assigns every retained
carrier node's key the zero-or-one value of the node's physical axis. -/
theorem retainedCarrierNode_carrierKey_axisValue
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (descriptors : List RouteDescriptor)
    (indexedSegmentsEq :
      (drawing graph).indexedSegments =
        routeDescriptorIndexedSegments descriptors)
    {node : CarrierNode}
    (nodeMember : node ∈ retainedDrawingCarrierNodes graph) :
    RouteDescriptorCarrierKeyAxisDatum.value descriptors
        (some node.carrierKey) =
      FixedAxisUnaryFields.value true node.isHorizontal := by
  cases node with
  | boundary boundary =>
      have boundaryMember :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMember
        simpa using nodeMember
      exact retainedBoundary_carrierKey_axisValue
        graph descriptors indexedSegmentsEq boundaryMember
  | terminal terminal =>
      have terminalMember :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at nodeMember
        simpa using nodeMember
      have member : terminal.indexed ∈
          routeDescriptorIndexedSegments descriptors := by
        rw [← indexedSegmentsEq]
        exact retainedSegmentTerminal_indexed_mem graph terminalMember
      exact
        RouteDescriptorCarrierKeyAxisDatum.value_some_segmentOccurrenceKey
          descriptors terminal.indexed terminal.translate member

end LeanTrominoes.PeriodicOrthocrossing
