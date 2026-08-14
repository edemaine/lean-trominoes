/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingHorizontalCrossings
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierOrder

/-!
# One-dimensional normalized retained-carrier clauses

For a horizontal source graph, a retained physical crossing's two segment
translates have the vertical coordinate extracted by crossing normalization.
Thus every retained carrier node normalizes with the vertical coordinate of
its supporting segment occurrence.  Consecutive nodes in a retained carrier
chain have the same occurrence key, so their normalized equality clauses are
one dimensional.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Both segment occurrences at a retained physical crossing have the
vertical translate extracted by crossing normalization. -/
theorem retainedCrossing_verticalTranslations_eq_shift
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {record : CrossingRecord}
    (recordMember : record ∈ retainedCrossings graph) :
    record.firstTranslate.2 = (crossingPeriodShift graph record).2 ∧
      record.secondTranslate.2 = (crossingPeriodShift graph record).2 := by
  have normalizedMember :=
    retainedCrossing_periodNormalize_mem_orientedCrossings
      graph recordMember
  have normalizedZero :=
    orientedCrossing_verticalTranslations_eq_zero
      isLocal horizontal normalizedMember
  have firstReconstruction := congrArg Prod.snd
    (periodNormalize_firstTranslate_add_shift graph record)
  have secondReconstruction := congrArg Prod.snd
    (periodNormalize_secondTranslate_add_shift graph record)
  simp only [Cell.add] at firstReconstruction secondReconstruction
  constructor <;> omega

/-- A retained crossover boundary normalizes with the vertical translate of
the segment occurrence that supports its selected side. -/
theorem retainedCrossingBoundary_normalize_vertical_eq_translate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {boundary : CrossingBoundary}
    (boundaryMember : boundary ∈ retainedCrossingBoundaries graph) :
    (normalizeCarrierNode graph (.boundary boundary)).2.2 =
      boundary.translate.2 := by
  have crossingMember :=
    retainedCrossingBoundary_crossing_mem graph boundaryMember
  have translations := retainedCrossing_verticalTranslations_eq_shift
    isLocal horizontal crossingMember
  rcases boundary with ⟨crossing, side⟩
  cases side
  · simpa [normalizeCarrierNode, CrossingBoundary.translate] using
      translations.1.symm
  · simpa [normalizeCarrierNode, CrossingBoundary.translate] using
      translations.1.symm
  · simpa [normalizeCarrierNode, CrossingBoundary.translate] using
      translations.2.symm
  · simpa [normalizeCarrierNode, CrossingBoundary.translate] using
      translations.2.symm

/-- Every retained carrier node normalizes with the vertical translate of
its supporting segment occurrence. -/
theorem retainedCarrierNode_normalize_vertical_eq_translate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {node : CarrierNode}
    (nodeMember : node ∈ retainedDrawingCarrierNodes graph) :
    (normalizeCarrierNode graph node).2.2 = node.translate.2 := by
  cases node with
  | terminal terminal => rfl
  | boundary boundary =>
      have boundaryMember :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMember
        simpa using nodeMember
      exact retainedCrossingBoundary_normalize_vertical_eq_translate
        isLocal horizontal boundaryMember

/-- The endpoints of a retained carrier-chain link normalize with equal
vertical shifts. -/
theorem retainedDrawingCompleteCarrierLinks_verticalEqual
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {link : EqualityLink CarrierNode}
    (linkMember : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    (normalizeCarrierNode graph link.first).2.2 =
      (normalizeCarrierNode graph link.second).2.2 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMember
  have commonKey :=
    retainedDrawingCompleteCarrierLinks_common_key graph linkMember
  have translateEqual : link.first.translate = link.second.translate := by
    simpa [CarrierNode.carrierKey_eq_indexed_translate,
      PeriodicGridDrawing.SegmentOccurrenceKey] using
        congrArg (fun key : Nat × Nat × Cell => key.2.2) commonKey
  exact
    (retainedCarrierNode_normalize_vertical_eq_translate
      isLocal horizontal endpoints.1).trans
      ((congrArg Prod.snd translateEqual).trans
        (retainedCarrierNode_normalize_vertical_eq_translate
          isLocal horizontal endpoints.2).symm)

end PeriodicOrthocrossing
end LeanTrominoes
