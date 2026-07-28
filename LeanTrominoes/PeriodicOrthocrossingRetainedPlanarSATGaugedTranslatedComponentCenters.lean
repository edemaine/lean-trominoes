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

end PeriodicOrthocrossing
end LeanTrominoes
