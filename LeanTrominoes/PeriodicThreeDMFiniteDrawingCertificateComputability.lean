import LeanTrominoes.PeriodicGridDrawingGeometryComputability
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate

/-!
# Computability of the finite periodic 3DM drawing certificate

The drawing search is effective only once every finite Boolean certificate
check is effective.  This module composes the primitive-recursive graph,
drawing, and exact integer-geometry operations into that combined verifier.
-/

noncomputable section

namespace LeanTrominoes

/-- Primitive-recursive bounded universal quantification over a computed
finite list. -/
theorem primrecPred_forall_mem {Input Element : Type*}
    [Primcodable Input] [Primcodable Element]
    {elements : Input → List Element} {predicate : Input → Element → Prop}
    (elementsPrimrec : Primrec elements)
    (predicatePrimrec : PrimrecRel predicate) :
    PrimrecPred fun input =>
      ∀ element ∈ elements input, predicate input element := by
  exact predicatePrimrec.swap.forall_mem_list.comp
    elementsPrimrec Primrec.id

namespace PeriodicThreeDM
namespace FiniteDrawingCertificate

set_option maxHeartbeats 300000

theorem positionInFundamentalSquareCheck_primrec :
    Primrec₂ positionInFundamentalSquareCheck := by
  change Primrec fun input : PeriodicGridDrawing × Cell =>
    positionInFundamentalSquareCheck input.1 input.2
  let period : Primrec fun input : PeriodicGridDrawing × Cell =>
      (input.1.gridSize : Int) :=
    Computability.int_ofNat_primrec.comp
      (PeriodicGridDrawing.gridSize_primrec.comp Primrec.fst)
  let positiveX : Primrec fun input : PeriodicGridDrawing × Cell =>
      decide ((0 : Int) < input.2.1) :=
    Computability.int_lt_primrec.decide.comp
      (Primrec.const (0 : Int)) (Primrec.fst.comp Primrec.snd)
  let upperX : Primrec fun input : PeriodicGridDrawing × Cell =>
      decide (input.2.1 < (input.1.gridSize : Int)) :=
    Computability.int_lt_primrec.decide.comp
      (Primrec.fst.comp Primrec.snd) period
  let positiveY : Primrec fun input : PeriodicGridDrawing × Cell =>
      decide ((0 : Int) < input.2.2) :=
    Computability.int_lt_primrec.decide.comp
      (Primrec.const (0 : Int)) (Primrec.snd.comp Primrec.snd)
  let upperY : Primrec fun input : PeriodicGridDrawing × Cell =>
      decide (input.2.2 < (input.1.gridSize : Int)) :=
    Computability.int_lt_primrec.decide.comp
      (Primrec.snd.comp Primrec.snd) period
  exact (Primrec.and.comp positiveX
    (Primrec.and.comp upperX
      (Primrec.and.comp positiveY upperY))).of_eq fun _ => rfl

theorem positionInFundamentalSquare_primrec :
    PrimrecRel PeriodicGridDrawing.PositionInFundamentalSquare := by
  change PrimrecPred fun input : PeriodicGridDrawing × Cell =>
    (0 : Int) < input.2.1 ∧
      input.2.1 < (input.1.gridSize : Int) ∧
      (0 : Int) < input.2.2 ∧
      input.2.2 < (input.1.gridSize : Int)
  let period : Primrec fun input : PeriodicGridDrawing × Cell =>
      (input.1.gridSize : Int) :=
    Computability.int_ofNat_primrec.comp
      (PeriodicGridDrawing.gridSize_primrec.comp Primrec.fst)
  exact (Computability.int_lt_primrec.comp
    (Primrec.const (0 : Int)) (Primrec.fst.comp Primrec.snd)).and
    ((Computability.int_lt_primrec.comp
      (Primrec.fst.comp Primrec.snd) period).and
    ((Computability.int_lt_primrec.comp
      (Primrec.const (0 : Int)) (Primrec.snd.comp Primrec.snd)).and
      (Computability.int_lt_primrec.comp
        (Primrec.snd.comp Primrec.snd) period)))

private abbrev RoutesMatchTaggedInput :=
  (PeriodicThreeDM × PeriodicGridDrawing) ×
    (PeriodicEdge PeriodicThreeDMVertex × Nat)

private def routesMatchTaggedRoute
    (combined : RoutesMatchTaggedInput) : List Cell :=
  combined.1.2.edgeRoute combined.2.2

private theorem routesMatchTaggedRoute_primrec :
    Primrec routesMatchTaggedRoute := by
  unfold routesMatchTaggedRoute
  exact PeriodicGridDrawing.edgeRoute_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)

private def routesMatchTaggedPosition (source : Bool)
    (combined : RoutesMatchTaggedInput) : Cell :=
  combined.1.2.vertexPosition combined.1.1.incidenceGraph
    (if source then combined.2.1.source else combined.2.1.target)

private theorem routesMatchTaggedPosition_primrec (source : Bool) :
    Primrec (routesMatchTaggedPosition source) := by
  unfold routesMatchTaggedPosition PeriodicGridDrawing.vertexPosition
  let graph : Primrec fun combined : RoutesMatchTaggedInput =>
      combined.1.1.incidenceGraph :=
    PeriodicThreeDM.incidenceGraph_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  let vertex : Primrec fun combined : RoutesMatchTaggedInput =>
      if source then combined.2.1.source else combined.2.1.target := by
    cases source
    · exact PeriodicEdge.target_primrec.comp
        (Primrec.fst.comp Primrec.snd)
    · exact PeriodicEdge.source_primrec.comp
        (Primrec.fst.comp Primrec.snd)
  exact (Primrec.list_getD (0, 0)).comp
    (PeriodicGridDrawing.vertexPositions_primrec.comp
      (Primrec.snd.comp Primrec.fst))
    (Primrec.list_idxOf.comp vertex
      (PeriodicGraph.vertices_primrec.comp graph))

private def routesMatchTaggedTranslation
    (combined : RoutesMatchTaggedInput) : Cell :=
  combined.1.2.periodTranslation combined.2.1.offset

private theorem routesMatchTaggedTranslation_primrec :
    Primrec routesMatchTaggedTranslation := by
  unfold routesMatchTaggedTranslation
  exact PeriodicGridDrawing.periodTranslation_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (PeriodicEdge.offset_primrec.comp
      (Primrec.fst.comp Primrec.snd))

private def routesMatchTaggedPredicate
    (combined : RoutesMatchTaggedInput) : Prop :=
  (routesMatchTaggedRoute combined).head? =
      some (routesMatchTaggedPosition true combined) ∧
    (routesMatchTaggedRoute combined).getLast? =
      some (Cell.add (routesMatchTaggedPosition false combined)
        (routesMatchTaggedTranslation combined))

private instance : DecidablePred routesMatchTaggedPredicate :=
  fun combined => by
    unfold routesMatchTaggedPredicate
    infer_instance

private theorem routesMatchTaggedPredicate_primrec :
    PrimrecPred routesMatchTaggedPredicate := by
  let expectedTarget : Primrec fun combined : RoutesMatchTaggedInput =>
      Cell.add (routesMatchTaggedPosition false combined)
        (routesMatchTaggedTranslation combined) :=
    Computability.cell_add_primrec.comp
      (routesMatchTaggedPosition_primrec false)
      routesMatchTaggedTranslation_primrec
  exact ((Primrec.eq.comp
    (Primrec.list_head?.comp routesMatchTaggedRoute_primrec)
    (Primrec.option_some.comp (routesMatchTaggedPosition_primrec true))).and
    (Primrec.eq.comp
      (Primrec.list_head?.comp
        (Primrec.list_reverse.comp routesMatchTaggedRoute_primrec))
      (Primrec.option_some.comp expectedTarget))).of_eq fun combined => by
        simp [routesMatchTaggedPredicate]

theorem routesMatchCheck_primrec :
    Primrec₂ routesMatchCheck := by
  change Primrec fun input : PeriodicThreeDM × PeriodicGridDrawing =>
    routesMatchCheck input.1 input.2
  let taggedEdges : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.edges.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicGraph.edges_primrec.comp
        (PeriodicThreeDM.incidenceGraph_primrec.comp Primrec.fst))
  have property : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      ∀ tagged ∈ input.1.incidenceGraph.edges.zipIdx,
        routesMatchTaggedPredicate (input, tagged) := by
    apply primrecPred_forall_mem taggedEdges
    exact routesMatchTaggedPredicate_primrec.primrecRel
  exact property.decide.of_eq fun input => by
    apply Bool.eq_iff_iff.mpr
    simp [routesMatchCheck, routesMatchTaggedPredicate,
      routesMatchTaggedRoute, routesMatchTaggedPosition,
      routesMatchTaggedTranslation]

theorem routesMatch_primrec : PrimrecRel fun
    (problem : PeriodicThreeDM) (drawing : PeriodicGridDrawing) =>
    drawing.RoutesMatch problem.incidenceGraph := by
  change PrimrecPred fun input : PeriodicThreeDM × PeriodicGridDrawing =>
    input.2.RoutesMatch input.1.incidenceGraph
  let taggedEdges : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.edges.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicGraph.edges_primrec.comp
        (PeriodicThreeDM.incidenceGraph_primrec.comp Primrec.fst))
  have property : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      ∀ tagged ∈ input.1.incidenceGraph.edges.zipIdx,
        routesMatchTaggedPredicate (input, tagged) := by
    apply primrecPred_forall_mem taggedEdges
    exact routesMatchTaggedPredicate_primrec.primrecRel
  exact property.of_eq fun input => by
    simp [PeriodicGridDrawing.RoutesMatch, routesMatchTaggedPredicate,
      routesMatchTaggedRoute, routesMatchTaggedPosition,
      routesMatchTaggedTranslation]

theorem compatibleCheck_primrec :
    Primrec₂ compatibleCheck := by
  change Primrec fun input : PeriodicThreeDM × PeriodicGridDrawing =>
    compatibleCheck input.1 input.2
  let graph : Primrec fun input : PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph :=
    PeriodicThreeDM.incidenceGraph_primrec.comp Primrec.fst
  let positions : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing => input.2.vertexPositions :=
    PeriodicGridDrawing.vertexPositions_primrec.comp Primrec.snd
  let routes : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing => input.2.edgeRoutes :=
    PeriodicGridDrawing.edgeRoutes_primrec.comp Primrec.snd
  let vertices : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.vertices :=
    PeriodicGraph.vertices_primrec.comp graph
  let edges : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.edges :=
    PeriodicGraph.edges_primrec.comp graph
  let positionLength : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.vertexPositions.length := Primrec.list_length.comp positions
  let vertexLength : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.vertices.length :=
    Primrec.list_length.comp vertices
  let routeLength : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.edgeRoutes.length := Primrec.list_length.comp routes
  let edgeLength : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.1.incidenceGraph.edges.length :=
    Primrec.list_length.comp edges
  let positionsNodup : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.vertexPositions.Nodup := by
    exact (Primrec.eq.comp
      (PeriodicThreeSATThree.dedup_primrec.comp positions)
      positions).of_eq fun input =>
        List.dedup_eq_self
  have positionsInside : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      ∀ position ∈ input.2.vertexPositions,
        input.2.PositionInFundamentalSquare position := by
    apply primrecPred_forall_mem positions
    exact (positionInFundamentalSquare_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).primrecRel
  let routesMatch : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.RoutesMatch input.1.incidenceGraph := by
    exact routesMatch_primrec.comp Primrec.fst Primrec.snd
  letI : DecidableRel
      PeriodicGridDrawing.PositionInFundamentalSquare :=
    fun drawing position => by
      unfold PeriodicGridDrawing.PositionInFundamentalSquare
      infer_instance
  letI : DecidablePred fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.RoutesMatch input.1.incidenceGraph :=
    fun input => by
      unfold PeriodicGridDrawing.RoutesMatch
      infer_instance
  let condition :=
    ((Primrec.eq.comp positionLength vertexLength).and
      ((Primrec.eq.comp routeLength edgeLength).and
      (positionsNodup.and (positionsInside.and routesMatch))))
  exact condition.decide.of_eq fun input => by
    apply Bool.eq_iff_iff.mpr
    simp [compatibleCheck, positionInFundamentalSquareCheck,
      routesMatchCheck, PeriodicGridDrawing.PositionInFundamentalSquare,
      PeriodicGridDrawing.RoutesMatch]

theorem orthogonalCheck_primrec :
    Primrec orthogonalCheck := by
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ indexed ∈ drawing.indexedSegments,
        indexed.segment.IsAxisAligned := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.indexedSegments_primrec
    exact (GridSegment.isAxisAligned_primrec.comp
      (IndexedGridSegment.segment_primrec.comp Primrec.snd)).primrecRel
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [orthogonalCheck]

theorem endpointBoundsCheck_primrec :
    Primrec endpointBoundsCheck := by
  letI : DecidablePred fun drawing : PeriodicGridDrawing =>
      ∀ indexed ∈ drawing.indexedSegments,
        drawing.PositionInExpandedSquare indexed.segment.start ∧
          drawing.PositionInExpandedSquare indexed.segment.finish :=
    fun drawing => by
      unfold PeriodicGridDrawing.PositionInExpandedSquare
      infer_instance
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ indexed ∈ drawing.indexedSegments,
        drawing.PositionInExpandedSquare indexed.segment.start ∧
          drawing.PositionInExpandedSquare indexed.segment.finish := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.indexedSegments_primrec
    change PrimrecPred fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
      combined.1.PositionInExpandedSquare combined.2.segment.start ∧
        combined.1.PositionInExpandedSquare combined.2.segment.finish
    let period : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        (combined.1.gridSize : Int) :=
      Computability.int_ofNat_primrec.comp
        (PeriodicGridDrawing.gridSize_primrec.comp Primrec.fst)
    let negativePeriod : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        -((combined.1.gridSize : Nat) : Int) :=
      Computability.int_negate_primrec.comp period
    let doublePeriod : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        (2 : Int) * combined.1.gridSize :=
      Computability.int_multiply_primrec.comp
        (Primrec.const (2 : Int)) period
    let segment : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        combined.2.segment :=
      IndexedGridSegment.segment_primrec.comp Primrec.snd
    let start : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        combined.2.segment.start :=
      GridSegment.start_primrec.comp segment
    let finish : Primrec fun combined :
        PeriodicGridDrawing × IndexedGridSegment =>
        combined.2.segment.finish :=
      GridSegment.finish_primrec.comp segment
    let inside {point :
        (PeriodicGridDrawing × IndexedGridSegment) → Cell}
        (pointPrimrec : Primrec point) :
        PrimrecPred fun combined :
          PeriodicGridDrawing × IndexedGridSegment =>
          -((combined.1.gridSize : Nat) : Int) < (point combined).1 ∧
            (point combined).1 < 2 * (combined.1.gridSize : Nat) ∧
            -((combined.1.gridSize : Nat) : Int) < (point combined).2 ∧
            (point combined).2 < 2 * (combined.1.gridSize : Nat) :=
      (Computability.int_lt_primrec.comp negativePeriod
        (Primrec.fst.comp pointPrimrec)).and
      ((Computability.int_lt_primrec.comp
        (Primrec.fst.comp pointPrimrec) doublePeriod).and
      ((Computability.int_lt_primrec.comp negativePeriod
        (Primrec.snd.comp pointPrimrec)).and
        (Computability.int_lt_primrec.comp
          (Primrec.snd.comp pointPrimrec) doublePeriod)))
    exact ((inside start).and (inside finish)).of_eq fun combined => by
      simp [PeriodicGridDrawing.PositionInExpandedSquare]
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [endpointBoundsCheck,
      PeriodicGridDrawing.PositionInExpandedSquare]

private abbrev IndexedSegmentPairContext :=
  (PeriodicGridDrawing × IndexedGridSegment) × IndexedGridSegment

private abbrev IndexedSegmentRelativeContext :=
  IndexedSegmentPairContext × Cell

private def segmentRelativeDrawing
    (context : IndexedSegmentRelativeContext) : PeriodicGridDrawing :=
  context.1.1.1

private theorem segmentRelativeDrawing_primrec :
    Primrec segmentRelativeDrawing := by
  unfold segmentRelativeDrawing
  exact Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

private def segmentRelativeFirst
    (context : IndexedSegmentRelativeContext) : IndexedGridSegment :=
  context.1.1.2

private theorem segmentRelativeFirst_primrec :
    Primrec segmentRelativeFirst := by
  unfold segmentRelativeFirst
  exact Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

private def segmentRelativeSecond
    (context : IndexedSegmentRelativeContext) : IndexedGridSegment :=
  context.1.2

private theorem segmentRelativeSecond_primrec :
    Primrec segmentRelativeSecond := by
  unfold segmentRelativeSecond
  exact Primrec.snd.comp Primrec.fst

private def segmentRelativeTranslation
    (context : IndexedSegmentRelativeContext) : Cell :=
  context.2

private theorem segmentRelativeTranslation_primrec :
    Primrec segmentRelativeTranslation := by
  exact Primrec.snd

private def segmentRelativeFirstSegment
    (context : IndexedSegmentRelativeContext) : GridSegment :=
  (segmentRelativeFirst context).segment

private theorem segmentRelativeFirstSegment_primrec :
    Primrec segmentRelativeFirstSegment := by
  exact (IndexedGridSegment.segment_primrec.comp
    segmentRelativeFirst_primrec).of_eq fun _ => rfl

private def segmentRelativePeriodTranslation
    (context : IndexedSegmentRelativeContext) : Cell :=
  (segmentRelativeDrawing context).periodTranslation
    (segmentRelativeTranslation context)

private theorem segmentRelativePeriodTranslation_primrec :
    Primrec segmentRelativePeriodTranslation := by
  exact (PeriodicGridDrawing.periodTranslation_primrec.comp
    segmentRelativeDrawing_primrec
    segmentRelativeTranslation_primrec).of_eq fun _ => rfl

private def segmentRelativeTranslatedFirst
    (context : IndexedSegmentRelativeContext) : GridSegment :=
  (segmentRelativeFirstSegment context).translate
    (segmentRelativePeriodTranslation context)

private theorem segmentRelativeTranslatedFirst_primrec :
    Primrec segmentRelativeTranslatedFirst := by
  exact (GridSegment.translate_primrec.comp
    segmentRelativePeriodTranslation_primrec
    segmentRelativeFirstSegment_primrec).of_eq fun _ => rfl

private def segmentRelativeInteriorPoints
    (context : IndexedSegmentRelativeContext) : List Cell :=
  PeriodicGridDrawing.segmentInteriorPoints
    (segmentRelativeTranslatedFirst context)

private theorem segmentRelativeInteriorPoints_primrec :
    Primrec segmentRelativeInteriorPoints := by
  unfold segmentRelativeInteriorPoints
  exact PeriodicGridDrawing.segmentInteriorPoints_primrec.comp
    segmentRelativeTranslatedFirst_primrec

theorem expandedFiniteRoutesAvoidInteriors_primrec :
    Primrec PeriodicGridDrawing.expandedFiniteRoutesAvoidInteriors := by
  have pointPredicate : PrimrecRel fun
      (context : IndexedSegmentRelativeContext) (point : Cell) =>
      PeriodicGridDrawing.SegmentOccurrenceKey context.1.1.2 context.2 =
          PeriodicGridDrawing.SegmentOccurrenceKey context.1.2 (0, 0) ∨
        ¬context.1.2.segment.Contains point := by
    change PrimrecPred fun combined :
        IndexedSegmentRelativeContext × Cell =>
      PeriodicGridDrawing.SegmentOccurrenceKey
          combined.1.1.1.2 combined.1.2 =
          PeriodicGridDrawing.SegmentOccurrenceKey
            combined.1.1.2 (0, 0) ∨
        ¬combined.1.1.2.segment.Contains combined.2
    let first : Primrec fun combined :
        IndexedSegmentRelativeContext × Cell =>
        segmentRelativeFirst combined.1 :=
      segmentRelativeFirst_primrec.comp Primrec.fst
    let second : Primrec fun combined :
        IndexedSegmentRelativeContext × Cell =>
        segmentRelativeSecond combined.1 :=
      segmentRelativeSecond_primrec.comp Primrec.fst
    let relative : Primrec fun combined :
        IndexedSegmentRelativeContext × Cell =>
        segmentRelativeTranslation combined.1 :=
      segmentRelativeTranslation_primrec.comp Primrec.fst
    let firstKey :=
      PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
        first relative
    let secondKey :=
      PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
        second (Primrec.const (0, 0))
    let contains := GridSegment.contains_primrec.comp
      (IndexedGridSegment.segment_primrec.comp second) Primrec.snd
    exact (Primrec.eq.comp firstKey secondKey).or contains.not
  have allPoints : PrimrecPred fun context :
      IndexedSegmentRelativeContext =>
      ∀ point ∈ segmentRelativeInteriorPoints context,
        PeriodicGridDrawing.SegmentOccurrenceKey context.1.1.2 context.2 =
            PeriodicGridDrawing.SegmentOccurrenceKey context.1.2 (0, 0) ∨
          ¬context.1.2.segment.Contains point :=
    primrecPred_forall_mem segmentRelativeInteriorPoints_primrec
      pointPredicate
  have allRelatives : PrimrecPred fun context :
      IndexedSegmentPairContext =>
      ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
        ∀ point ∈ segmentRelativeInteriorPoints (context, relative),
          PeriodicGridDrawing.SegmentOccurrenceKey context.1.2 relative =
              PeriodicGridDrawing.SegmentOccurrenceKey context.2 (0, 0) ∨
            ¬context.2.segment.Contains point := by
    apply primrecPred_forall_mem
      (Primrec.const PeriodicGridDrawing.doubleNeighborTranslations)
    exact allPoints.primrecRel
  have allSeconds : PrimrecPred fun context :
      PeriodicGridDrawing × IndexedGridSegment =>
      ∀ second ∈ context.1.indexedSegments,
        ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
          ∀ point ∈ segmentRelativeInteriorPoints
              ((context, second), relative),
            PeriodicGridDrawing.SegmentOccurrenceKey context.2 relative =
                PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0) ∨
              ¬second.segment.Contains point := by
    apply primrecPred_forall_mem
      (PeriodicGridDrawing.indexedSegments_primrec.comp Primrec.fst)
    exact allRelatives.primrecRel
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ first ∈ drawing.indexedSegments,
        ∀ second ∈ drawing.indexedSegments,
          ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
            ∀ point ∈ segmentRelativeInteriorPoints
                (((drawing, first), second), relative),
              PeriodicGridDrawing.SegmentOccurrenceKey first relative =
                  PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0) ∨
                ¬second.segment.Contains point := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.indexedSegments_primrec
    exact allSeconds.primrecRel
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [PeriodicGridDrawing.expandedFiniteRoutesAvoidInteriors,
      segmentRelativeInteriorPoints, segmentRelativeTranslatedFirst,
      segmentRelativeFirstSegment, segmentRelativePeriodTranslation,
      segmentRelativeFirst, segmentRelativeDrawing,
      segmentRelativeTranslation]

private abbrev VertexSegmentContext :=
  (PeriodicGridDrawing × Cell) × IndexedGridSegment

private abbrev VertexSegmentRelativeContext :=
  VertexSegmentContext × Cell

private def vertexSegmentRelativeTranslatedSegment
    (context : VertexSegmentRelativeContext) : GridSegment :=
  context.1.2.segment.translate
    (context.1.1.1.periodTranslation context.2)

private theorem vertexSegmentRelativeTranslatedSegment_primrec :
    Primrec vertexSegmentRelativeTranslatedSegment := by
  let drawing : Primrec fun context : VertexSegmentRelativeContext =>
      context.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let indexed : Primrec fun context : VertexSegmentRelativeContext =>
      context.1.2 := Primrec.snd.comp Primrec.fst
  let translation : Primrec fun context : VertexSegmentRelativeContext =>
      context.1.1.1.periodTranslation context.2 :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      drawing Primrec.snd
  let segment : Primrec fun context : VertexSegmentRelativeContext =>
      context.1.2.segment :=
    IndexedGridSegment.segment_primrec.comp indexed
  exact (GridSegment.translate_primrec.comp
    translation segment).of_eq fun _ => rfl

theorem finiteVerticesAvoidRouteInteriors_primrec :
    Primrec PeriodicGridDrawing.finiteVerticesAvoidRouteInteriors := by
  have relativePredicate : PrimrecRel fun
      (context : VertexSegmentContext) (relative : Cell) =>
      ¬(vertexSegmentRelativeTranslatedSegment
          (context, relative)).InteriorContains context.1.2 := by
    change PrimrecPred fun combined : VertexSegmentRelativeContext =>
      ¬(vertexSegmentRelativeTranslatedSegment combined).InteriorContains
        combined.1.1.2
    exact (GridSegment.interiorContains_primrec.comp
      vertexSegmentRelativeTranslatedSegment_primrec
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).not
  have allRelatives : PrimrecPred fun context : VertexSegmentContext =>
      ∀ relative ∈ PeriodicOrthocrossing.neighborTranslations,
        ¬(context.2.segment.translate
            (context.1.1.periodTranslation relative)).InteriorContains
          context.1.2 := by
    apply primrecPred_forall_mem
      (Primrec.const PeriodicOrthocrossing.neighborTranslations)
    exact relativePredicate
  have allSegments : PrimrecPred fun context :
      PeriodicGridDrawing × Cell =>
      ∀ indexed ∈ context.1.indexedSegments,
        ∀ relative ∈ PeriodicOrthocrossing.neighborTranslations,
          ¬(indexed.segment.translate
              (context.1.periodTranslation relative)).InteriorContains
            context.2 := by
    apply primrecPred_forall_mem
      (PeriodicGridDrawing.indexedSegments_primrec.comp Primrec.fst)
    exact allRelatives.primrecRel
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ vertex ∈ drawing.vertexPositions,
        ∀ indexed ∈ drawing.indexedSegments,
          ∀ relative ∈ PeriodicOrthocrossing.neighborTranslations,
            ¬(indexed.segment.translate
                (drawing.periodTranslation relative)).InteriorContains
              vertex := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.vertexPositions_primrec
    exact allSegments.primrecRel
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [PeriodicGridDrawing.finiteVerticesAvoidRouteInteriors]

theorem expandedFiniteRoutesHaveDisjointInteriors_primrec :
    Primrec
      PeriodicGridDrawing.expandedFiniteRoutesHaveDisjointInteriors := by
  have relativePredicate : PrimrecRel fun
      (context : IndexedSegmentPairContext) (relative : Cell) =>
      PeriodicGridDrawing.SegmentOccurrenceKey context.1.2 relative =
          PeriodicGridDrawing.SegmentOccurrenceKey context.2 (0, 0) ∨
        ¬GridSegment.InteriorsMeet
          (segmentRelativeTranslatedFirst (context, relative))
          context.2.segment := by
    change PrimrecPred fun combined : IndexedSegmentRelativeContext =>
      PeriodicGridDrawing.SegmentOccurrenceKey
          combined.1.1.2 combined.2 =
          PeriodicGridDrawing.SegmentOccurrenceKey combined.1.2 (0, 0) ∨
        ¬GridSegment.InteriorsMeet
          (segmentRelativeTranslatedFirst combined)
          combined.1.2.segment
    let firstKey :=
      PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
        segmentRelativeFirst_primrec segmentRelativeTranslation_primrec
    let secondKey :=
      PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
        segmentRelativeSecond_primrec (Primrec.const (0, 0))
    let secondSegment := IndexedGridSegment.segment_primrec.comp
      segmentRelativeSecond_primrec
    exact (Primrec.eq.comp firstKey secondKey).or
      (GridSegment.interiorsMeet_primrec.comp
        segmentRelativeTranslatedFirst_primrec secondSegment).not
  have allRelatives : PrimrecPred fun context :
      IndexedSegmentPairContext =>
      ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
        PeriodicGridDrawing.SegmentOccurrenceKey context.1.2 relative =
            PeriodicGridDrawing.SegmentOccurrenceKey context.2 (0, 0) ∨
          ¬GridSegment.InteriorsMeet
            (segmentRelativeTranslatedFirst (context, relative))
            context.2.segment := by
    apply primrecPred_forall_mem
      (Primrec.const PeriodicGridDrawing.doubleNeighborTranslations)
    exact relativePredicate
  have allSeconds : PrimrecPred fun context :
      PeriodicGridDrawing × IndexedGridSegment =>
      ∀ second ∈ context.1.indexedSegments,
        ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
          PeriodicGridDrawing.SegmentOccurrenceKey context.2 relative =
              PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0) ∨
            ¬GridSegment.InteriorsMeet
              (segmentRelativeTranslatedFirst
                ((context, second), relative)) second.segment := by
    apply primrecPred_forall_mem
      (PeriodicGridDrawing.indexedSegments_primrec.comp Primrec.fst)
    exact allRelatives.primrecRel
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ first ∈ drawing.indexedSegments,
        ∀ second ∈ drawing.indexedSegments,
          ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
            PeriodicGridDrawing.SegmentOccurrenceKey first relative =
                PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0) ∨
              ¬GridSegment.InteriorsMeet
                (segmentRelativeTranslatedFirst
                  (((drawing, first), second), relative))
                second.segment := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.indexedSegments_primrec
    exact allSeconds.primrecRel
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [PeriodicGridDrawing.expandedFiniteRoutesHaveDisjointInteriors,
      segmentRelativeTranslatedFirst, segmentRelativeFirstSegment,
      segmentRelativePeriodTranslation, segmentRelativeFirst,
      segmentRelativeDrawing, segmentRelativeTranslation]

private abbrev IndexedRoutePointPairContext :=
  (PeriodicGridDrawing × IndexedRoutePoint) × IndexedRoutePoint

private abbrev IndexedRoutePointRelativeContext :=
  IndexedRoutePointPairContext × Cell

theorem expandedFiniteRoutePointsMeetOnlyAtEndpoints_primrec :
    Primrec
      PeriodicGridDrawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints := by
  have relativePredicate : PrimrecRel fun
      (context : IndexedRoutePointPairContext) (relative : Cell) =>
      PeriodicGridDrawing.RoutePointOccurrenceKey context.1.2 relative =
          PeriodicGridDrawing.RoutePointOccurrenceKey context.2 (0, 0) ∨
        Cell.add context.1.2.point
            (context.1.1.periodTranslation relative) ≠ context.2.point ∨
        (context.1.2.IsEndpoint ∧ context.2.IsEndpoint) := by
    change PrimrecPred fun combined : IndexedRoutePointRelativeContext =>
      PeriodicGridDrawing.RoutePointOccurrenceKey
          combined.1.1.2 combined.2 =
          PeriodicGridDrawing.RoutePointOccurrenceKey combined.1.2 (0, 0) ∨
        Cell.add combined.1.1.2.point
            (combined.1.1.1.periodTranslation combined.2) ≠
          combined.1.2.point ∨
        (combined.1.1.2.IsEndpoint ∧ combined.1.2.IsEndpoint)
    let pair : Primrec fun combined : IndexedRoutePointRelativeContext =>
        combined.1 := Primrec.fst
    let first : Primrec fun combined : IndexedRoutePointRelativeContext =>
        combined.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp pair)
    let second : Primrec fun combined : IndexedRoutePointRelativeContext =>
        combined.1.2 := Primrec.snd.comp pair
    let drawing : Primrec fun combined : IndexedRoutePointRelativeContext =>
        combined.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp pair)
    let relative : Primrec fun combined : IndexedRoutePointRelativeContext =>
        combined.2 := Primrec.snd
    let firstKey :=
      PeriodicGridDrawing.routePointOccurrenceKey_primrec.comp
        first relative
    let secondKey :=
      PeriodicGridDrawing.routePointOccurrenceKey_primrec.comp
        second (Primrec.const (0, 0))
    let firstPoint := IndexedRoutePoint.point_primrec.comp first
    let secondPoint := IndexedRoutePoint.point_primrec.comp second
    let translation :=
      PeriodicGridDrawing.periodTranslation_primrec.comp drawing relative
    let translatedPoint := Computability.cell_add_primrec.comp
      firstPoint translation
    let sameOccurrence := Primrec.eq.comp firstKey secondKey
    let distinctPoints :=
      (Primrec.eq.comp translatedPoint secondPoint).not
    let endpoints :=
      (IndexedRoutePoint.isEndpoint_primrec.comp first).and
        (IndexedRoutePoint.isEndpoint_primrec.comp second)
    exact sameOccurrence.or (distinctPoints.or endpoints)
  have allRelatives : PrimrecPred fun context :
      IndexedRoutePointPairContext =>
      ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
        PeriodicGridDrawing.RoutePointOccurrenceKey context.1.2 relative =
            PeriodicGridDrawing.RoutePointOccurrenceKey context.2 (0, 0) ∨
          Cell.add context.1.2.point
              (context.1.1.periodTranslation relative) ≠ context.2.point ∨
          (context.1.2.IsEndpoint ∧ context.2.IsEndpoint) := by
    apply primrecPred_forall_mem
      (Primrec.const PeriodicGridDrawing.doubleNeighborTranslations)
    exact relativePredicate
  have allSeconds : PrimrecPred fun context :
      PeriodicGridDrawing × IndexedRoutePoint =>
      ∀ second ∈ context.1.indexedRoutePoints,
        ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
          PeriodicGridDrawing.RoutePointOccurrenceKey context.2 relative =
              PeriodicGridDrawing.RoutePointOccurrenceKey second (0, 0) ∨
            Cell.add context.2.point
                (context.1.periodTranslation relative) ≠ second.point ∨
            (context.2.IsEndpoint ∧ second.IsEndpoint) := by
    apply primrecPred_forall_mem
      (PeriodicGridDrawing.indexedRoutePoints_primrec.comp Primrec.fst)
    exact allRelatives.primrecRel
  have property : PrimrecPred fun drawing : PeriodicGridDrawing =>
      ∀ first ∈ drawing.indexedRoutePoints,
        ∀ second ∈ drawing.indexedRoutePoints,
          ∀ relative ∈ PeriodicGridDrawing.doubleNeighborTranslations,
            PeriodicGridDrawing.RoutePointOccurrenceKey first relative =
                PeriodicGridDrawing.RoutePointOccurrenceKey second (0, 0) ∨
              Cell.add first.point (drawing.periodTranslation relative) ≠
                second.point ∨
              (first.IsEndpoint ∧ second.IsEndpoint) := by
    apply primrecPred_forall_mem
      PeriodicGridDrawing.indexedRoutePoints_primrec
    exact allSeconds.primrecRel
  exact property.decide.of_eq fun drawing => by
    apply Bool.eq_iff_iff.mpr
    simp [PeriodicGridDrawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints]

theorem verifies_primrec : Primrec₂ verifies := by
  change Primrec fun input : PeriodicThreeDM × PeriodicGridDrawing =>
    verifies input.1 input.2
  let compatible : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      compatibleCheck input.1 input.2 :=
    compatibleCheck_primrec.comp Primrec.fst Primrec.snd
  let orthogonal : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      orthogonalCheck input.2 :=
    orthogonalCheck_primrec.comp Primrec.snd
  let endpointBounds : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      endpointBoundsCheck input.2 :=
    endpointBoundsCheck_primrec.comp Primrec.snd
  let routesAvoidInteriors : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.expandedFiniteRoutesAvoidInteriors :=
    expandedFiniteRoutesAvoidInteriors_primrec.comp Primrec.snd
  let verticesAvoidRouteInteriors : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.finiteVerticesAvoidRouteInteriors :=
    finiteVerticesAvoidRouteInteriors_primrec.comp Primrec.snd
  let routesHaveDisjointInteriors : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.expandedFiniteRoutesHaveDisjointInteriors :=
    expandedFiniteRoutesHaveDisjointInteriors_primrec.comp Primrec.snd
  let routePointsMeetOnlyAtEndpoints : Primrec fun input :
      PeriodicThreeDM × PeriodicGridDrawing =>
      input.2.expandedFiniteRoutePointsMeetOnlyAtEndpoints :=
    expandedFiniteRoutePointsMeetOnlyAtEndpoints_primrec.comp Primrec.snd
  exact (Primrec.and.comp compatible
    (Primrec.and.comp orthogonal
      (Primrec.and.comp endpointBounds
        (Primrec.and.comp routesAvoidInteriors
          (Primrec.and.comp verticesAvoidRouteInteriors
            (Primrec.and.comp routesHaveDisjointInteriors
              routePointsMeetOnlyAtEndpoints)))))).of_eq fun _ => rfl

theorem verifies_computable : Computable₂ verifies :=
  verifies_primrec.to_comp

end FiniteDrawingCertificate
end PeriodicThreeDM
end LeanTrominoes
