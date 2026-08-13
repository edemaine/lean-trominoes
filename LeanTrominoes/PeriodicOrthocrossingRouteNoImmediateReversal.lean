/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineNoImmediateReversalJoin
import LeanTrominoes.PeriodicOrthocrossingRouteNoImmediateReversalComponents

/-!
# No immediate reversals in complete orthocrossing routes

The source fanout enters the edge core while heading north, and the edge
core enters the reversed target fanout while heading south.  The component
certificates therefore splice into a no-immediate-reversal certificate for
every complete constructed edge route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every complete route constructed for a local edge avoids immediate
reversals. -/
theorem constructedEdgeRoute_hasNoImmediateReversal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    AxisDirection.HasNoImmediateReversal
      (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2) := by
  let sourceCenter :=
    vertexX (graph.vertices.idxOf taggedEdge.1.source)
  let targetCenter :=
    vertexX (graph.vertices.idxOf taggedEdge.1.target)
  let sourceColumn :=
    portX graph (sourcePort taggedEdge.1 taggedEdge.2)
  let targetColumn :=
    portX graph (targetPort taggedEdge.1 taggedEdge.2)
  let targetTranslate :=
    Cell.scale (drawingGridSize graph : Int) taggedEdge.1.offset
  let sourceFanout := fanout sourceCenter sourceColumn
  let core := edgeCore graph taggedEdge.1 taggedEdge.2
  let targetFanout :=
    translatePolyline targetTranslate
      (fanout targetCenter targetColumn).reverse
  let sourceMiddle : Cell := (sourceColumn, 3)
  let targetMiddle : Cell :=
    Cell.add (targetColumn, 3) targetTranslate
  have sourceNoReversal :
      AxisDirection.HasNoImmediateReversal sourceFanout :=
    fanout_hasNoImmediateReversal sourceCenter sourceColumn
  have coreNoReversal :
      AxisDirection.HasNoImmediateReversal core :=
    edgeCore_hasNoImmediateReversal
      wellFormed degree edgeMem edgeLocal
  have targetNoReversal :
      AxisDirection.HasNoImmediateReversal targetFanout :=
    translated_reverse_fanout_hasNoImmediateReversal
      targetCenter targetColumn targetTranslate
  have sourceOrthogonal : OrthogonalPolyline sourceFanout :=
    fanout_orthogonal sourceCenter sourceColumn
  have coreOrthogonal : OrthogonalPolyline core :=
    edgeCore_orthogonal wellFormed degree edgeMem edgeLocal
  have targetOrthogonal : OrthogonalPolyline targetFanout :=
    translated_reverse_fanout_orthogonal
      targetCenter targetColumn targetTranslate
  have sourceLong : 2 ≤ sourceFanout.length :=
    fanout_length_ge_two sourceCenter sourceColumn
  have coreLong : 2 ≤ core.length :=
    edgeCore_length_ge_two graph taggedEdge.1 taggedEdge.2
  have targetLong : 2 ≤ targetFanout.length :=
    translated_reverse_fanout_length_ge_two
      targetCenter targetColumn targetTranslate
  have sourceLast :
      sourceFanout.getLast? = some sourceMiddle := by
    simp [sourceFanout, sourceMiddle, sourceColumn]
  have coreHead :
      core.head? = some sourceMiddle := by
    simp [core, sourceMiddle, sourceColumn]
  have coreLast :
      core.getLast? = some targetMiddle := by
    simp [core, targetMiddle, targetColumn, targetTranslate]
  have targetHead :
      targetFanout.head? = some targetMiddle := by
    dsimp [targetFanout, targetMiddle, targetTranslate,
      targetCenter, targetColumn]
    by_cases same :
        vertexX (graph.vertices.idxOf taggedEdge.1.target) =
          portX graph (targetPort taggedEdge.1 taggedEdge.2)
    · simp [translatePolyline, fanout, same, Cell.add, add_comm]
    · simp [translatePolyline, fanout, same, Cell.add, add_comm]
  have sourceCompatible :
      AxisDirection.polylineFirstDirection core ≠
        (AxisDirection.polylineLastDirection sourceFanout).opposite := by
    rw [edgeCore_firstDirection edgeMem edgeLocal,
      fanout_lastDirection]
    simp [AxisDirection.opposite]
  have sourceCoreNoReversal :
      AxisDirection.HasNoImmediateReversal
        (joinPolylines sourceFanout core) := by
    have joined :=
      AxisDirection.HasNoImmediateReversal.joinAtEndpoint_of_compatible
        sourceNoReversal coreNoReversal
        sourceOrthogonal coreOrthogonal
        sourceLong coreLong sourceLast coreHead sourceCompatible
    simpa [joinPolylines, LeanTrominoes.joinAtEndpoint] using joined
  have sourceCoreOrthogonal :
      OrthogonalPolyline
        (joinPolylines sourceFanout core) :=
    isChain_joinPolylines sourceOrthogonal coreOrthogonal
      (by rw [sourceLast, coreHead])
  have sourceCoreLong :
      2 ≤ (joinPolylines sourceFanout core).length := by
    unfold joinPolylines
    simp only [List.length_append]
    omega
  have sourceCoreLast :
      (joinPolylines sourceFanout core).getLast? =
        some targetMiddle := by
    rw [joinPolylines_getLast?_of_second coreLong]
    exact coreLast
  have sourceCoreLastDirection :
      AxisDirection.polylineLastDirection
          (joinPolylines sourceFanout core) =
        .south := by
    have preserved :=
      AxisDirection.polylineLastDirection_joinAtEndpoint
        sourceLast coreHead coreLong
    rw [edgeCore_lastDirection edgeMem edgeLocal] at preserved
    simpa [joinPolylines, LeanTrominoes.joinAtEndpoint] using preserved
  have targetCompatible :
      AxisDirection.polylineFirstDirection targetFanout ≠
        (AxisDirection.polylineLastDirection
          (joinPolylines sourceFanout core)).opposite := by
    rw [translated_reverse_fanout_firstDirection,
      sourceCoreLastDirection]
    simp [AxisDirection.opposite]
  have joined :=
    AxisDirection.HasNoImmediateReversal.joinAtEndpoint_of_compatible
      sourceCoreNoReversal targetNoReversal
      sourceCoreOrthogonal targetOrthogonal
      sourceCoreLong targetLong sourceCoreLast targetHead
      targetCompatible
  change
    AxisDirection.HasNoImmediateReversal
      (joinPolylines
        (joinPolylines sourceFanout core) targetFanout)
  simpa [joinPolylines, LeanTrominoes.joinAtEndpoint] using joined

end PeriodicOrthocrossing
end LeanTrominoes
