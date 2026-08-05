import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-!
# Final gauged retained Figure 9 presentation

The finite compatibility certificate is completed by the vertex-bound
module.  This module transports unit steps and route simplicity through the
last clause ordering and variable gauge, combines them with global relative
route separation, and packages the resulting planar and continuously planar
incidence presentations.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Translating each canonical route by its whole-period gauge shift
preserves unit lattice steps of the finite incidence drawing. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (unitSteps :
      (incidenceDrawing source placement routes).HasUnitSteps) :
    (incidenceDrawing
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).HasUnitSteps := by
  intro gaugedRoute gaugedRouteMember
  change gaugedRoute ∈
    incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
    at gaugedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map] at gaugedRouteMember
  rcases List.mem_map.mp gaugedRouteMember with
    ⟨incidence, incidenceMember, gaugedRouteEq⟩
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, _literal, clauseMember, _literalMember, _incidenceEq⟩
  have sourceRouteMember :
      routes incidence.clauseIndex incidence.literalIndex ∈
        (incidenceDrawing source placement routes).edgeRoutes := by
    change routes incidence.clauseIndex incidence.literalIndex ∈
      incidenceEdgeRoutes source routes
    rw [incidenceEdgeRoutes_eq_metadata_map]
    exact List.mem_map.mpr
      ⟨incidence,
        List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have sourceUnitSteps := unitSteps _ sourceRouteMember
  have transportedRouteEq :
      gaugedRoute =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (variableGaugeCanonicalRouteShift gauge clause))
          (routes incidence.clauseIndex incidence.literalIndex) := by
    rw [← gaugedRouteEq]
    change
      variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          incidence.clauseIndex incidence.literalIndex = _
    exact variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes clauseMember
  rw [transportedRouteEq]
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain
      (Cell.add
        (placement.translation
          (variableGaugeCanonicalRouteShift gauge clause)))
  · intro first second step
    exact AxisDirection.IsUnitAxisStep.translate step _
  · exact sourceUnitSteps

/-- Translating each canonical route by its whole-period gauge shift
preserves geometric simplicity of every stored route. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (simple :
      ∀ route ∈ (incidenceDrawing source placement routes).edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈
        (incidenceDrawing
          (source.variableGauge gauge)
          (placement.variableGauge gauge)
          (variableGaugeCanonicalIncidenceRoutes
            source placement gauge routes)).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro gaugedRoute gaugedRouteMember
  change gaugedRoute ∈
    incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
    at gaugedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map] at gaugedRouteMember
  rcases List.mem_map.mp gaugedRouteMember with
    ⟨incidence, incidenceMember, gaugedRouteEq⟩
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, _literal, clauseMember, _literalMember, _incidenceEq⟩
  have sourceRouteMember :
      routes incidence.clauseIndex incidence.literalIndex ∈
        (incidenceDrawing source placement routes).edgeRoutes := by
    change routes incidence.clauseIndex incidence.literalIndex ∈
      incidenceEdgeRoutes source routes
    rw [incidenceEdgeRoutes_eq_metadata_map]
    exact List.mem_map.mpr
      ⟨incidence,
        List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have sourceSimple := simple _ sourceRouteMember
  have transportedRouteEq :
      gaugedRoute =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (variableGaugeCanonicalRouteShift gauge clause))
          (routes incidence.clauseIndex incidence.literalIndex) := by
    rw [← gaugedRouteEq]
    change
      variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          incidence.clauseIndex incidence.literalIndex = _
    exact variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes clauseMember
  rw [transportedRouteEq]
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      sourceSimple _

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance finalGaugedPresentationVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Final clause ordering preserves unit lattice steps of every normalized
incidence route. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).HasUnitSteps := by
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes]
  apply PositionedPeriodicCNF.incidenceDrawing_hasUnitSteps_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_unitSteps
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember =>
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_unitSteps
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember

/-- Final clause ordering and its whole-period anchor translations preserve
geometric simplicity of every normalized incidence route. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ route ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes]
  apply PositionedPeriodicCNF.incidenceDrawing_routesSimple_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  rcases PositionedPeriodicCNF.exists_sourceLiteral_of_orderedLiteral_mem
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      clauseEq, literalEq, orderedRouteEq⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  subst clause
  subst literal
  rw [PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection,
    sourceClauseLookup, orderedRouteEq]
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      _

/-- The quotient gauge preserves unit lattice steps of the final drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).HasUnitSteps := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
    using
      PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_hasUnitSteps
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_hasUnitSteps
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- The quotient gauge preserves geometric simplicity of every stored final
route. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ route ∈
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
    using
      PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesSimple
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_routesSimple
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- The metadata-indexed separation certificate supplies complete relative
separation of the anonymous stored route occurrences. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_relativeLiftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).RelativeLiftedRoutesAvoidEachOther := by
  rw [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
  exact
    PositionedPeriodicCNF.incidenceDrawing_relativeLiftedRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_pos
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_relativeIncidenceRoutesAvoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- The fully ordered and canonically gauged drawing is continuously planar
and its lifted route occurrences meet only at advertised endpoints. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_relativeLiftedRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_routesSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The final ordered, canonically gauged formula has a complete planar
orthogonal incidence presentation with no residual geometric hypotheses. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.PlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source) where
  routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  periodPositive :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_pos
      source
  compatible := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isCompatible
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  orthogonal := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isOrthogonal
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  planar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).1.1

/-- The final presentation also has exact continuous route-interior
separation, as required before ribbon thickening. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source) where
  toPlanarIncidencePresentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  continuouslyPlanar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).1

end PeriodicOrthocrossing
end LeanTrominoes
