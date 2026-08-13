/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedComponentAlignmentSeparation

/-!
# Macrocell centers under physical source translation

A final periodic occurrence carries both an external quotient shift and the
anchor gauge of its retained source.  Comparing two physical occurrences
therefore translates one retained source by an arbitrary lattice vector,
which need not itself remain in the finite retained halo.

This file develops center uniqueness directly for such translated physical
components.  These lemmas let a common macrocell center recover exact
component alignment without first proving that the translated source was
enumerated.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Equality after erasing a bend's occurrence translation, together with
the translated occurrence coordinate, recovers equality of the complete
translated bend records. -/
theorem RouteBend.periodTranslate_eq_of_eraseTranslation_eq
    (first second : RouteBend)
    (shift : Cell)
    (geometryEq :
      first.eraseTranslation = second.eraseTranslation)
    (translateEq :
      Cell.add first.translate shift = second.translate) :
    first.periodTranslate shift = second := by
  rcases first with
    ⟨firstRouteIndex, firstIncomingSegmentIndex, firstTranslate,
      firstIncomingStart, firstBend, firstOutgoingFinish⟩
  rcases second with
    ⟨secondRouteIndex, secondIncomingSegmentIndex, secondTranslate,
      secondIncomingStart, secondBend, secondOutgoingFinish⟩
  simp only [RouteBend.eraseTranslation, RouteBend.periodTranslate,
    RouteBend.mk.injEq] at geometryEq ⊢
  exact
    ⟨geometryEq.1, geometryEq.2.1, translateEq,
      geometryEq.2.2.2.1, geometryEq.2.2.2.2.1,
      geometryEq.2.2.2.2.2⟩

/-- A drawing point still uniquely identifies a bend when the first bend is
translated by an arbitrary lattice vector, even when that translated bend
falls outside the finite bend enumeration. -/
theorem drawingRouteBend_periodTranslate_eq_of_drawingPoint_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (shift : Cell)
    (pointEq :
      (first.periodTranslate shift).drawingPoint graph =
        second.drawingPoint graph) :
    first.periodTranslate shift = second := by
  rcases drawingRouteBend_centerPlacement
      graph isLocal firstMem with
    ⟨firstEdge, firstEdgeIndex,
      firstPlacement, firstPlacementIndex,
      firstEdgeMem, firstPlacementMem,
      firstRouteEq, firstIndexEq, firstPointEq⟩
  rcases drawingRouteBend_centerPlacement
      graph isLocal secondMem with
    ⟨secondEdge, secondEdgeIndex,
      secondPlacement, secondPlacementIndex,
      secondEdgeMem, secondPlacementMem,
      secondRouteEq, secondIndexEq, secondPointEq⟩
  have firstPlacementListMem :
      firstPlacement ∈
        routeBendCenterPlacements
          graph firstEdge firstEdgeIndex :=
    List.fst_mem_of_mem_zipIdx firstPlacementMem
  have secondPlacementListMem :
      secondPlacement ∈
        routeBendCenterPlacements
          graph secondEdge secondEdgeIndex :=
    List.fst_mem_of_mem_zipIdx secondPlacementMem
  have firstValid :=
    routeBendCenterPlacements_kind_valid
      firstEdgeMem firstPlacementListMem
  have secondValid :=
    routeBendCenterPlacements_kind_valid
      secondEdgeMem secondPlacementListMem
  have firstTranslatedPointEq :
      (first.periodTranslate shift).drawingPoint graph =
        Cell.add
          (firstPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add (Cell.add first.translate shift)
              firstPlacement.offset)) := by
    rw [RouteBend.drawingPoint_periodTranslate, firstPointEq]
    rcases firstPlacement.kind.position graph with
      ⟨positionX, positionY⟩
    rcases first.translate with ⟨translateX, translateY⟩
    rcases shift with ⟨shiftX, shiftY⟩
    rcases firstPlacement.offset with ⟨offsetX, offsetY⟩
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
    constructor <;> ring
  have normalizedPointEq :
      Cell.add
          (firstPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add (Cell.add first.translate shift)
              firstPlacement.offset)) =
        Cell.add
          (secondPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add second.translate secondPlacement.offset)) := by
    rw [← firstTranslatedPointEq, ← secondPointEq]
    exact pointEq
  have normalizedUnique :=
    PeriodicGridDrawing.translatedHalfOpenPositions_eq
      (drawing graph)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree firstValid)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree secondValid)
      normalizedPointEq
  have kindEq :
      firstPlacement.kind = secondPlacement.kind :=
    RouteBendCenterKind.eq_of_position_eq
      wellFormed degree firstValid secondValid
        normalizedUnique.1
  have firstKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph firstEdge firstEdgeIndex firstPlacementListMem
  have secondKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph secondEdge secondEdgeIndex secondPlacementListMem
  have edgeIndexEq :
      firstEdgeIndex = secondEdgeIndex :=
    firstKindIndex.symm.trans
      ((congrArg RouteBendCenterKind.edgeIndex kindEq).trans
        secondKindIndex)
  have taggedEdgeEq :
      (firstEdge, firstEdgeIndex) =
        (secondEdge, secondEdgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstEdgeMem secondEdgeMem edgeIndexEq
  have edgeEq : firstEdge = secondEdge :=
    congrArg Prod.fst taggedEdgeEq
  subst secondEdge
  rw [← edgeIndexEq] at secondPlacementMem
  have taggedPlacementEq :
      (firstPlacement, firstPlacementIndex) =
        (secondPlacement, secondPlacementIndex) :=
    routeBendCenterPlacements_tagged_eq_of_kind_eq
      graph firstEdge firstEdgeIndex
        firstPlacementMem secondPlacementMem kindEq
  have placementEq :
      firstPlacement = secondPlacement :=
    congrArg Prod.fst taggedPlacementEq
  have placementIndexEq :
      firstPlacementIndex = secondPlacementIndex :=
    congrArg Prod.snd taggedPlacementEq
  have translateOffsetEq :
      Cell.add (Cell.add first.translate shift)
          firstPlacement.offset =
        Cell.add second.translate secondPlacement.offset :=
    normalizedUnique.2
  have translateEq :
      Cell.add first.translate shift = second.translate := by
    have offsetEq :
        firstPlacement.offset = secondPlacement.offset :=
      congrArg RouteBendCenterPlacement.offset placementEq
    rw [offsetEq] at translateOffsetEq
    exact
      Cell.add_right_injective
        secondPlacement.offset translateOffsetEq
  have geometryEq :
      first.eraseTranslation = second.eraseTranslation :=
    drawingRouteBends_eraseTranslation_eq_of_identity_eq
      graph firstMem secondMem
      (firstRouteEq.trans
        (edgeIndexEq.trans secondRouteEq.symm))
      (firstIndexEq.trans
        (placementIndexEq.trans secondIndexEq.symm))
  exact first.periodTranslate_eq_of_eraseTranslation_eq
    second shift geometryEq translateEq

/-- Equality of lifted clause-vertex centers identifies an arbitrarily
translated routed-clause site with a retained routed-clause site. -/
theorem clauseRouteSitePeriodTranslate_eq_of_liftedPosition_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : ClauseRouteSite}
    (firstMem : first ∈ drawingClauseRouteSites formula)
    (secondMem : second ∈ drawingClauseRouteSites formula)
    (shift : Cell)
    (positionEq :
      liftedIncidenceVertexPosition formula
          (.clause first.1) (Cell.add first.2 shift) =
        liftedIncidenceVertexPosition formula
          (.clause second.1) second.2) :
    clauseRouteSitePeriodTranslate first shift = second := by
  have unique :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingClauseRouteSite_vertex_mem formula firstMem)
      (drawingClauseRouteSite_vertex_mem formula secondMem)
      positionEq
  apply Prod.ext
  · exact CNFVertex.clause.inj unique.1
  · exact unique.2

/-- Equality of lifted variable-vertex centers identifies an arbitrarily
translated routed-variable site with a retained routed-variable site. -/
theorem variableRouteSitePeriodTranslate_eq_of_liftedPosition_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : VariableRouteSite Variable}
    (firstMem : first ∈ drawingVariableRouteSites formula)
    (secondMem : second ∈ drawingVariableRouteSites formula)
    (shift : Cell)
    (positionEq :
      liftedIncidenceVertexPosition formula
          (.variable first.1) (Cell.add first.2 shift) =
        liftedIncidenceVertexPosition formula
          (.variable second.1) second.2) :
    variableRouteSitePeriodTranslate first shift = second := by
  have unique :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingVariableRouteSite_vertex_mem formula firstMem)
      (drawingVariableRouteSite_vertex_mem formula secondMem)
      positionEq
  apply Prod.ext
  · exact CNFVertex.variable.inj unique.1
  · exact unique.2

/-- A crossing point still uniquely identifies an oriented crossing after
an arbitrary common period translation of the first record.  Normalization
brings both physical records back to the canonical crossing quotient, while
the common physical point recovers the same discarded quotient shift. -/
theorem orientedCrossing_periodTranslate_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (shift : Cell)
    (pointEq :
      (first.periodTranslate graph shift).point = second.point) :
    first.periodTranslate graph shift = second := by
  let translated := first.periodTranslate graph shift
  have translatedNormalizedMem :
      translated.periodNormalize graph ∈ orientedCrossings graph := by
    rw [show translated.periodNormalize graph =
        first.periodNormalize graph by
      exact CrossingRecord.periodNormalize_periodTranslate
        graph first shift]
    exact periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal firstMem
  have secondNormalizedMem :
      second.periodNormalize graph ∈ orientedCrossings graph :=
    periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal secondMem
  have periodShiftEq :
      crossingPeriodShift graph translated =
        crossingPeriodShift graph second := by
    simp only [crossingPeriodShift]
    rw [pointEq]
  have normalizedPointEq :
      (translated.periodNormalize graph).point =
        (second.periodNormalize graph).point := by
    simp only [CrossingRecord.periodNormalize]
    rw [pointEq, periodShiftEq]
  have normalizedEq :
      translated.periodNormalize graph =
        second.periodNormalize graph :=
    orientedCrossing_eq_of_point_eq
      wellFormed degree isLocal
      (orientedCrossings_subset_orientedCrossingHalo
        graph translatedNormalizedMem)
      (orientedCrossings_subset_orientedCrossingHalo
        graph secondNormalizedMem)
      normalizedPointEq
  change translated = second
  rw [← CrossingRecord.periodNormalize_periodTranslate_shift
      graph translated,
    ← CrossingRecord.periodNormalize_periodTranslate_shift
      graph second,
    normalizedEq, periodShiftEq]

/-- A retained crossover center cannot coincide with an arbitrary period
translate of an enumerated route-bend center.  The bend's classified
adjacent segments and normalized center placement come from its finite
representative; only their occurrence coordinate is translated. -/
theorem
    orientedCrossing_point_ne_drawingRouteBend_periodTranslate_drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph)
    (shift : Cell) :
    crossing.point ≠
      (routeBend.periodTranslate shift).drawingPoint graph := by
  intro pointEq
  rcases drawingRouteBend_adjacentClassifiedSegments
      graph routeBendMem with
    ⟨edge, edgeIndex, incoming, outgoing,
      edgeMem, incomingMem, outgoingMem,
      routeIndexEq, incomingIndexEq, outgoingIndexEq,
      incomingSegmentEq, outgoingSegmentEq⟩
  have geometry :=
    drawingRouteBend_cornerGeometry
      wellFormed degree isLocal routeBendMem
  rcases geometry.incomingAligned with
    incomingHorizontal | incomingVertical
  · have incomingHorizontal' :
        incoming.1.segment.IsHorizontal := by
      rw [incomingSegmentEq]
      exact incomingHorizontal
    apply
      orientedCrossing_point_ne_horizontal_classified_endpoint
        wellFormed degree isLocal crossingMem
        edgeMem incomingMem incomingHorizontal'
        (Cell.add routeBend.translate shift) .finish
    rw [incomingSegmentEq]
    simpa [RouteBend.drawingPoint,
      RouteBend.periodTranslate] using pointEq
  · rcases geometry.outgoingAligned with
      outgoingHorizontal | outgoingVertical
    · have outgoingHorizontal' :
          outgoing.1.segment.IsHorizontal := by
        rw [outgoingSegmentEq]
        exact outgoingHorizontal
      apply
        orientedCrossing_point_ne_horizontal_classified_endpoint
          wellFormed degree isLocal crossingMem
          edgeMem outgoingMem outgoingHorizontal'
          (Cell.add routeBend.translate shift) .start
      rw [outgoingSegmentEq]
      simpa [RouteBend.drawingPoint,
        RouteBend.periodTranslate] using pointEq
    · have incomingVertical' :
          incoming.1.segment.IsVertical := by
        rw [incomingSegmentEq]
        exact incomingVertical
      have outgoingVertical' :
          outgoing.1.segment.IsVertical := by
        rw [outgoingSegmentEq]
        exact outgoingVertical
      rcases drawingRouteBend_centerPlacement
          graph isLocal routeBendMem with
        ⟨placementEdge, placementEdgeIndex,
          placement, placementIndex,
          placementEdgeMem, placementMem,
          placementRouteIndexEq, placementIndexEq,
          placementPointEq⟩
      have edgeIndexEq :
          placementEdgeIndex = edgeIndex := by
        rw [← placementRouteIndexEq, ← routeIndexEq]
      have taggedEdgeEq :
          (placementEdge, placementEdgeIndex) =
            (edge, edgeIndex) :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          placementEdgeMem edgeMem edgeIndexEq
      have placementEdgeEq :
          placementEdge = edge :=
        congrArg Prod.fst taggedEdgeEq
      subst placementEdge
      rw [edgeIndexEq] at placementMem
      have incomingPlacementIndexEq :
          incoming.2 = placementIndex := by
        omega
      have outgoingPlacementIndexEq :
          outgoing.2 = placementIndex + 1 := by
        omega
      rcases
          routeBendCenterPlacement_kind_port_of_adjacent_vertical
            graph edge edgeIndex placementMem
            incomingMem outgoingMem
            incomingPlacementIndexEq
            outgoingPlacementIndexEq
            incomingVertical' outgoingVertical' with
        ⟨port, placementKindEq⟩
      apply
        orientedCrossing_point_snd_ne_portRow crossingMem
          (Cell.add
            (Cell.add routeBend.translate shift)
            placement.offset).2
      have translatedPlacementPointEq :
          (routeBend.periodTranslate shift).drawingPoint graph =
            Cell.add
              (placement.kind.position graph)
              ((drawing graph).periodTranslation
                (Cell.add
                  (Cell.add routeBend.translate shift)
                  placement.offset)) := by
        rw [RouteBend.drawingPoint_periodTranslate,
          placementPointEq]
        rcases placement.kind.position graph with
          ⟨positionX, positionY⟩
        rcases routeBend.translate with
          ⟨translateX, translateY⟩
        rcases shift with ⟨shiftX, shiftY⟩
        rcases placement.offset with ⟨offsetX, offsetY⟩
        simp [PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale]
        constructor <;> ring
      have pointYEq :=
        congrArg Prod.snd
          (pointEq.trans translatedPlacementPointEq)
      rw [placementKindEq] at pointYEq
      simpa [RouteBendCenterKind.position,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale] using pointYEq

/-- Cancel one drawing-period translation from the left side of a physical
point equality. -/
theorem point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second shift : Cell)
    (equal :
      Cell.add first ((drawing graph).periodTranslation shift) =
        second) :
    first =
      Cell.add second
        ((drawing graph).periodTranslation
          (Cell.sub (0, 0) shift)) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.sub, Cell.scale, Prod.mk.injEq] at equal ⊢
  constructor
  · linear_combination equal.1
  · linear_combination equal.2

set_option maxHeartbeats 1200000 in
/-- If an arbitrary translate of one retained noncarrier component and a
second retained noncarrier component have the same macrocell center, then
the components align exactly, except that two routed-variable arms may share
their translated variable site. -/
theorem
    retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift center : Cell)
    (firstCenterEq :
      ((first.source.periodTranslate formula shift).component
        |>.macrocellCenter formula) = some center)
    (secondCenterEq :
      second.source.component.macrocellCenter formula = some center) :
    second.source.component =
        (first.source.periodTranslate formula shift).component ∨
      ∃ site firstArm firstLink secondArm secondLink,
        (first.source.periodTranslate formula shift).component =
            .routedVariable site firstArm firstLink ∧
          second.source.component =
            .routedVariable site secondArm secondLink := by
  let graph := PeriodicCNF.incidenceGraph formula
  rcases first with ⟨firstClause, firstSource⟩
  rcases second with ⟨secondClause, secondSource⟩
  cases firstSource with
  | carrier firstLink firstIndex =>
      simp [DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at firstCenterEq
  | crossover firstCrossing firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          left
          have pointEq :
              (firstCrossing.periodTranslate graph shift).point =
                secondCrossing.point := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have crossingEq :=
            orientedCrossing_periodTranslate_eq_of_point_eq
              wellFormed degree isLocal
              firstValid.1 secondValid.1 shift pointEq
          simp only [DrawingPlanarSATClauseSource.periodTranslate,
            DrawingPlanarSATClauseSource.component]
          congr 1
          exact crossingEq.symm
      | bend secondBend secondIndex =>
          exfalso
          have pointEq :
              (firstCrossing.periodTranslate graph shift).point =
                secondBend.drawingPoint graph := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have backEq :
              firstCrossing.point =
                (secondBend.periodTranslate
                  (Cell.sub (0, 0) shift)).drawingPoint graph := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                graph firstCrossing.point
                  (secondBend.drawingPoint graph) shift
                  (by
                    simpa [CrossingRecord.periodTranslate] using pointEq)
            rw [RouteBend.drawingPoint_periodTranslate]
            exact cancelled
          exact
            (orientedCrossing_point_ne_drawingRouteBend_periodTranslate_drawingPoint
              wellFormed degree isLocal firstValid.1
              (List.mem_dedup.mp secondValid.1)
              (Cell.sub (0, 0) shift))
              backEq
      | routedClause secondSite =>
          exfalso
          have pointEq :
              (firstCrossing.periodTranslate graph shift).point =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have backEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub (0, 0) shift)) := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                graph firstCrossing.point
                  (liftedIncidenceVertexPosition formula
                    (.clause secondSite.1) secondSite.2)
                  shift
                  (by
                    simpa [CrossingRecord.periodTranslate] using pointEq)
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact cancelled
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2
                (Cell.sub (0, 0) shift)))
              (by simpa [liftedIncidenceVertexPosition] using backEq)
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          have pointEq :
              (firstCrossing.periodTranslate graph shift).point =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have backEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub (0, 0) shift)) := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                graph firstCrossing.point
                  (liftedIncidenceVertexPosition formula
                    (.variable secondSite.1) secondSite.2)
                  shift
                  (by
                    simpa [CrossingRecord.periodTranslate] using pointEq)
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact cancelled
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2
                (Cell.sub (0, 0) shift)))
              (by simpa [liftedIncidenceVertexPosition] using backEq)
  | bend firstBend firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          have pointEq :
              (firstBend.periodTranslate shift).drawingPoint graph =
                secondCrossing.point := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          exact
            (orientedCrossing_point_ne_drawingRouteBend_periodTranslate_drawingPoint
              wellFormed degree isLocal secondValid.1
              (List.mem_dedup.mp firstValid.1) shift)
              pointEq.symm
      | bend secondBend secondIndex =>
          left
          have pointEq :
              (firstBend.periodTranslate shift).drawingPoint graph =
                secondBend.drawingPoint graph := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have bendEq :=
            drawingRouteBend_periodTranslate_eq_of_drawingPoint_eq
              graph wellFormed degree isLocal
              (List.mem_dedup.mp firstValid.1)
              (List.mem_dedup.mp secondValid.1)
              shift pointEq
          simp only [DrawingPlanarSATClauseSource.periodTranslate,
            DrawingPlanarSATClauseSource.component]
          congr 1
          exact bendEq.symm
      | routedClause secondSite =>
          exfalso
          have pointEq :
              (firstBend.periodTranslate shift).drawingPoint graph =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have backEq :
              firstBend.drawingPoint graph =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub (0, 0) shift)) := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                graph (firstBend.drawingPoint graph)
                  (liftedIncidenceVertexPosition formula
                    (.clause secondSite.1) secondSite.2)
                  shift
                  (by
                    simpa only [RouteBend.drawingPoint_periodTranslate]
                      using pointEq)
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact cancelled
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2
                (Cell.sub (0, 0) shift))
              (List.mem_dedup.mp firstValid.1))
              (by simpa [liftedIncidenceVertexPosition] using backEq)
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          have pointEq :
              (firstBend.periodTranslate shift).drawingPoint graph =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have backEq :
              firstBend.drawingPoint graph =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub (0, 0) shift)) := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                graph (firstBend.drawingPoint graph)
                  (liftedIncidenceVertexPosition formula
                    (.variable secondSite.1) secondSite.2)
                  shift
                  (by
                    simpa only [RouteBend.drawingPoint_periodTranslate]
                      using pointEq)
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact cancelled
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2
                (Cell.sub (0, 0) shift))
              (List.mem_dedup.mp firstValid.1))
              (by simpa [liftedIncidenceVertexPosition] using backEq)
  | routedClause firstSite =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          have pointEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2 shift) =
                secondCrossing.point := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 shift))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq.symm)
      | bend secondBend secondIndex =>
          exfalso
          have pointEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2 shift) =
                secondBend.drawingPoint graph := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 shift)
              (List.mem_dedup.mp secondValid.1))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq.symm)
      | routedClause secondSite =>
          left
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2 shift) =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have siteEq :=
            clauseRouteSitePeriodTranslate_eq_of_liftedPosition_eq
              formula firstValid.1 secondValid.1 shift positionEq
          simp only [DrawingPlanarSATClauseSource.periodTranslate,
            DrawingPlanarSATClauseSource.component]
          congr 1
          exact siteEq.symm
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2 shift) =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have impossible :=
            liftedDrawingVertexPosition_eq graph
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              positionEq
          cases impossible.1
  | routedVariable firstSite firstArmIndex firstArm firstLink firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          have pointEq :
              liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2 shift) =
                secondCrossing.point := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 shift))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq.symm)
      | bend secondBend secondIndex =>
          exfalso
          have pointEq :
              liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2 shift) =
                secondBend.drawingPoint graph := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 shift)
              (List.mem_dedup.mp secondValid.1))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq.symm)
      | routedClause secondSite =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2 shift) =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have impossible :=
            liftedDrawingVertexPosition_eq graph
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              positionEq
          cases impossible.1
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          right
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2 shift) =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [graph, clauseRouteSitePeriodTranslate,
              variableRouteSitePeriodTranslate,
              DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          have siteEq :=
            variableRouteSitePeriodTranslate_eq_of_liftedPosition_eq
              formula firstValid.1 secondValid.1 shift positionEq
          refine
            ⟨variableRouteSitePeriodTranslate firstSite shift,
              firstArm,
              planarSATNodeLinkPeriodTranslate graph firstLink shift,
              secondArm, secondLink, ?_, ?_⟩
          · rfl
          · simp only [siteEq,
              DrawingPlanarSATClauseSource.component]

end PeriodicOrthocrossing
end LeanTrominoes
