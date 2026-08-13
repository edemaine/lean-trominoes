/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteCorrectness
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-!
# Unit-step planarity for polarity-normalized routes

The threefold route refinement is immediately unit-subdivided.  This file
proves that every prefix, reverse middle edge, suffix, and gauge translation
used by polarity normalization retains genuine unit lattice steps.  The
assembled normalized drawing therefore satisfies the integer-grid planarity
predicate automatically.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Every genuine refined source route consists of unit lattice steps. -/
theorem refinedRoute_unitSteps_of_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (refinedRoute presentation.routes clauseIndex literalIndex).IsChain
      AxisDirection.IsUnitAxisStep := by
  apply AxisDirection.unitSubdividePolyline_unitSteps
  exact PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
    (sourceRoute_orthogonal_of_refined_members presentation
      clauseMember literalMember)
    refinementFactor_positive

/-- Translating a unit-step polyline preserves every unit step. -/
theorem unitSteps_translate
    (route : List Cell)
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep)
    (offset : Cell) :
    (PeriodicOrthocrossing.translatePolyline offset route).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain (Cell.add offset)
  · intro first second step
    exact AxisDirection.IsUnitAxisStep.translate step offset
  · exact unitSteps

/-- Points two and one of a four-point unit route form a unit-step reverse
middle edge. -/
theorem reverse_middle_unitSteps
    (route : List Cell)
    (length : 4 ≤ route.length)
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep) :
    [route.getD 2 (0, 0), route.getD 1 (0, 0)].IsChain
      AxisDirection.IsUnitAxisStep := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              have secondThird :
                  AxisDirection.IsUnitAxisStep second third :=
                (List.isChain_cons_cons.mp
                  (List.isChain_cons_cons.mp unitSteps).2).1
              simpa using secondThird.symm

/-- Every genuine output incidence can be traced to the exact source
occurrence whose refined route it uses. -/
theorem exists_raw_source_of_output_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {outputClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral (PolarityNormalizedVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈ outputClause.literals.zipIdx) :
    ∃ metadata sourceLiteral sourceLiteralIndex,
      (clauseMetadata source sourcePlacement presentation.routes)[outputClauseIndex]? =
        some metadata ∧
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx ∧
      ((metadata.origin = .normalized ∧
          sourceLiteralIndex = outputLiteralIndex) ∨
        (metadata.origin = .complement sourceLiteralIndex sourceLiteral ∧
          (outputLiteralIndex = 0 ∨ outputLiteralIndex = 1))) := by
  have formulaClauseMember :
      (outputClause, outputClauseIndex) ∈
        (PeriodicOneInThreePolarityNormalizationPositioned.formula
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).clauses.zipIdx := by
    simpa [rawFormula] using outputClauseMember
  rcases
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_lookup
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) formulaClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEq⟩
  have rawMetadataLookup :
      (clauseMetadata source sourcePlacement presentation.routes)[outputClauseIndex]? =
        some metadata := by
    simpa [clauseMetadata] using metadataLookup
  have metadataIndexLt :
      outputClauseIndex <
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement))[outputClauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have sourceClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement presentation.routes)
      (refinedSource source sourcePlacement) metadataMember
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have normalizedLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
              metadata.sourceClauseIndex metadata.sourceClause).literals.zipIdx := by
        rw [← normalizedClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have normalizedLiteralLookup :
          (PeriodicOneInThreePolarityNormalization.normalizeClause
            metadata.sourceClauseIndex metadata.sourceClause.literals)[outputLiteralIndex]? =
              some outputLiteral := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause]
          using (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
      rw [PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?]
          at normalizedLiteralLookup
      rcases Option.map_eq_some_iff.mp normalizedLiteralLookup with
        ⟨sourceLiteral, sourceLiteralLookup, _outputLiteralEq⟩
      have sourceLiteralMember :
          (sourceLiteral, outputLiteralIndex) ∈
            metadata.sourceClause.literals.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
      exact ⟨metadata, sourceLiteral, outputLiteralIndex,
        rawMetadataLookup, sourceClauseMember, sourceLiteralMember,
        Or.inl ⟨originEq, rfl⟩⟩
  | complement sourceLiteralIndex sourceLiteral =>
      have complementValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
              (rawPositions sourcePlacement presentation.routes)
              metadata.sourceClauseIndex sourceLiteralIndex
              sourceLiteral).literals.zipIdx := by
        rw [← complementClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have outputLiteralIndexLt : outputLiteralIndex < 2 := by
        have := List.snd_lt_of_mem_zipIdx complementLiteralMember
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause] using this
      have outputIndexCases :
          outputLiteralIndex = 0 ∨ outputLiteralIndex = 1 := by
        omega
      exact ⟨metadata, sourceLiteral, sourceLiteralIndex,
        rawMetadataLookup, complementValid.1, complementValid.2.1,
        Or.inr ⟨originEq, outputIndexCases⟩⟩

/-- Every raw route chosen from a genuine output incidence consists entirely
of unit lattice steps. -/
theorem rawIncidenceRoutes_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {outputClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral (PolarityNormalizedVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈ outputClause.literals.zipIdx) :
    (rawIncidenceRoutes source sourcePlacement presentation.routes
      outputClauseIndex outputLiteralIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, originData⟩
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    outputClauseIndex outputLiteralIndex metadataLookup]
  have refinedUnitSteps := refinedRoute_unitSteps_of_members
    presentation sourceClauseMember sourceLiteralMember
  rcases originData with normalized | complement
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    subst sourceLiteralIndex
    by_cases compatible :
        sourceLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            outputLiteralIndex
    · rw [rawRouteForMetadata_normalized_compatible
        sourcePlacement presentation.routes metadata sourceLiteral
        outputLiteralIndex originEq
        ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
        compatible]
      exact refinedUnitSteps
    · rw [rawRouteForMetadata_normalized_incompatible
        sourcePlacement presentation.routes metadata sourceLiteral
        outputLiteralIndex originEq
        ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
        compatible]
      exact List.IsChain.take refinedUnitSteps 2
  · rcases complement with ⟨originEq, outputIndexCases⟩
    have routeLength := refinedRoute_length_ge_four_of_members
      presentation sourceClauseMember sourceLiteralMember
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · subst outputLiteralIndex
      rw [rawRouteForMetadata_complement_fresh
        sourcePlacement presentation.routes metadata sourceLiteral
        sourceLiteralIndex originEq]
      apply unitSteps_translate
      simpa [routePoint] using
        reverse_middle_unitSteps
          (refinedRoute presentation.routes metadata.sourceClauseIndex
            sourceLiteralIndex)
          routeLength refinedUnitSteps
    · subst outputLiteralIndex
      rw [rawRouteForMetadata_complement_original
        sourcePlacement presentation.routes metadata sourceLiteral
        sourceLiteralIndex originEq]
      exact unitSteps_translate _ (List.IsChain.drop refinedUnitSteps 2) _

/-- Every route stored by the raw normalized incidence drawing consists of
unit lattice steps. -/
theorem rawIncidenceDrawing_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes))
        |>.HasUnitSteps := by
  intro route routeMember
  change route ∈
    PositionedPeriodicCNF.incidenceEdgeRoutes
      (rawFormula source sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
    at routeMember
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map]
      at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEq⟩
  subst route
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  exact rawIncidenceRoutes_unitSteps presentation
    outputClauseMember outputLiteralMember

/-- Whole-period translation of every canonical route preserves a unit-step
certificate for the assembled incidence drawing. -/
theorem variableGaugeCanonicalIncidenceRoutes_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (unitSteps :
      (PositionedPeriodicCNF.incidenceDrawing source sourcePlacement routes)
        |>.HasUnitSteps) :
    (PositionedPeriodicCNF.incidenceDrawing
      (source.variableGauge gauge)
      (sourcePlacement.variableGauge gauge)
      (PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes
        source sourcePlacement gauge routes)).HasUnitSteps := by
  intro gaugedRoute gaugedRouteMember
  change gaugedRoute ∈
    PositionedPeriodicCNF.incidenceEdgeRoutes
      (source.variableGauge gauge)
      (PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes
        source sourcePlacement gauge routes)
    at gaugedRouteMember
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
    PositionedPeriodicCNF.erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map] at gaugedRouteMember
  rcases List.mem_map.mp gaugedRouteMember with
    ⟨incidence, incidenceMember, gaugedRouteEq⟩
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, _literal, clauseMember, _literalMember, _incidenceEq⟩
  have sourceRouteMember :
      routes incidence.clauseIndex incidence.literalIndex ∈
        (PositionedPeriodicCNF.incidenceDrawing
          source sourcePlacement routes).edgeRoutes := by
    change routes incidence.clauseIndex incidence.literalIndex ∈
      PositionedPeriodicCNF.incidenceEdgeRoutes source routes
    rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map]
    exact List.mem_map.mpr
      ⟨incidence, List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have sourceUnitSteps := unitSteps _ sourceRouteMember
  have transportedRouteEq :
      gaugedRoute =
        PeriodicOrthocrossing.translatePolyline
          (sourcePlacement.translation
            (PositionedPeriodicCNF.variableGaugeCanonicalRouteShift
              gauge clause))
          (routes incidence.clauseIndex incidence.literalIndex) := by
    rw [← gaugedRouteEq]
    change
      PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes
          source sourcePlacement gauge routes
          incidence.clauseIndex incidence.literalIndex = _
    exact
      PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes_of_clause_mem
        source sourcePlacement gauge routes clauseMember
  rw [transportedRouteEq]
  exact unitSteps_translate _ sourceUnitSteps _

/-- Every route in the final gauged polarity-normalized incidence drawing is
a unit-step route. -/
theorem incidenceDrawing_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.HasUnitSteps := by
  simpa [formula, placement, incidenceRoutes] using
    variableGaugeCanonicalIncidenceRoutes_hasUnitSteps
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawIncidenceDrawing_hasUnitSteps presentation)

/-- Unit subdivision makes the final polarity-normalized incidence drawing
planar in the project's integer-grid sense. -/
theorem incidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.IsPlanar := by
  exact PeriodicGridDrawing.isPlanar_of_hasUnitSteps
    (incidenceDrawing_hasUnitSteps presentation)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
