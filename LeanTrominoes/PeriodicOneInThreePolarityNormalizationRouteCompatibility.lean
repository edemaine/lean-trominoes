/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertexInjectivity

/-!
# Compatibility of the polarity-normalized incidence drawing

Every retained source vertex keeps the fundamental-square bounds of the
threefold-scaled source presentation, and the two new subdivision vertices
have explicit strict bounds.  Together with final vertex injectivity and the
already certified route endpoints, these facts supply the complete finite
compatibility certificate.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The final gauged placement has the same period as the threefold-scaled
source placement. -/
theorem placement_period_eq_refinedPlacement_period
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (placement sourcePlacement routes).period =
      (refinedPlacement sourcePlacement).period := by
  rw [placement, PeriodicVariablePlacement.variableGauge_period,
    rawPlacement_period]

/-- The final normalized incidence drawing has the refined source period as
its fundamental-square side length. -/
theorem incidenceDrawing_gridSize_eq_refinedPlacement_period
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes)).gridSize =
        (refinedPlacement sourcePlacement).period := by
  have periodPositive :
      0 < (placement sourcePlacement presentation.routes).period := by
    rw [placement_period_eq_refinedPlacement_period]
    exact (scaledSourcePresentation presentation).periodPositive
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    (formula source sourcePlacement presentation.routes)
    (placement sourcePlacement presentation.routes)
    (incidenceRoutes source sourcePlacement presentation.routes)
    periodPositive,
    placement_period_eq_refinedPlacement_period]

/-- Explicit coordinate bounds against the refined period are exactly the
bounds required by the final drawing. -/
theorem finalPositionInFundamentalSquare_of_refinedBounds
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (position : Cell)
    (bounds :
      0 < position.1 ∧
        position.1 < (refinedPlacement sourcePlacement).period ∧
        0 < position.2 ∧
        position.2 < (refinedPlacement sourcePlacement).period) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.PositionInFundamentalSquare position := by
  unfold PeriodicGridDrawing.PositionInFundamentalSquare
  rw [incidenceDrawing_gridSize_eq_refinedPlacement_period presentation]
  exact bounds

/-- Every scaled source vertex remains inside the final drawing's identical
fundamental square. -/
theorem sourceVertex_in_finalFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (position : Cell)
    (positionMember :
      position ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes).vertexPositions) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.PositionInFundamentalSquare position := by
  have sourceBounds :=
    (scaledSourcePresentation presentation).compatible.2.2.2.2.1
      position positionMember
  unfold PeriodicGridDrawing.PositionInFundamentalSquare at sourceBounds
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement)
    (scaledSourcePresentation presentation).routes
    (scaledSourcePresentation presentation).periodPositive] at sourceBounds
  exact finalPositionInFundamentalSquare_of_refinedBounds
    presentation position sourceBounds

/-- Every position in the complete final incidence-vertex list lies strictly
inside its fundamental square. -/
theorem finalIncidenceVertexPositions_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ∀ position ∈
        PositionedPeriodicCNF.incidenceVertexPositions
          (formula source sourcePlacement presentation.routes)
          (placement sourcePlacement presentation.routes),
      (PositionedPeriodicCNF.incidenceDrawing
        (formula source sourcePlacement presentation.routes)
        (placement sourcePlacement presentation.routes)
        (incidenceRoutes source sourcePlacement presentation.routes))
          |>.PositionInFundamentalSquare position := by
  intro position positionMember
  rw [PositionedPeriodicCNF.incidenceVertexPositions_eq_variablePrefix_append,
    List.mem_append] at positionMember
  rcases positionMember with variablePositionMember | clausePositionMember
  · rw [PeriodicCNF.incidenceVariableVertices, List.map_map,
      List.mem_map] at variablePositionMember
    rcases variablePositionMember with
      ⟨atom, atomMember, positionEq⟩
    have finalAtomMember := List.mem_dedup.mp atomMember
    cases atom with
    | inl originalAtom =>
        have originalMember :=
          originalOccurrence_mem_refinedSource finalAtomMember
        have sourcePositionMember :=
          refinedVariablePosition_mem_sourceVertices
            presentation originalMember
        rw [← positionEq]
        simpa [PositionedPeriodicCNF.incidenceVariableVertexPosition,
          Function.comp_def] using
          sourceVertex_in_finalFundamentalSquare presentation
            ((refinedPlacement sourcePlacement).position originalAtom)
            sourcePositionMember
    | inr fresh =>
        rcases freshOccurrence_valid_of_final_member finalAtomMember with
          ⟨sourceClause, sourceClauseMember,
            sourceLiteralMember, _incompatible⟩
        have pointBounds :=
          (routePoints_one_two_inSquare presentation
            sourceClauseMember sourceLiteralMember).1
        rw [← positionEq]
        simpa [PositionedPeriodicCNF.incidenceVariableVertexPosition,
          Function.comp_def, placement_fresh_position] using
          finalPositionInFundamentalSquare_of_refinedBounds presentation
            (routePoint presentation.routes fresh 1) pointBounds
  · rcases List.mem_map.mp clausePositionMember with
      ⟨finalClause, finalClauseMember, positionEq⟩
    rcases List.mem_iff_getElem?.mp finalClauseMember with
      ⟨finalClauseIndex, finalClauseLookup⟩
    have indexedClauseMember :
        (finalClause, finalClauseIndex) ∈
          (formula source sourcePlacement presentation.routes).clauses.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr finalClauseLookup
    rcases exists_metadata_of_final_clause_member
        source sourcePlacement presentation.routes indexedClauseMember with
      ⟨metadata, _metadataLookup, metadataMember,
        sourceClauseMember, finalClauseEq⟩
    have baseMetadataMember :
        metadata ∈
          PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement) := by
      simpa only [clauseMetadata] using metadataMember
    cases originEq : metadata.origin with
    | normalized =>
        have rawClauseEq :=
          PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            baseMetadataMember originEq
        have canonicalEq :
            PositionedPeriodicCNF.canonicalClausePosition
                (placement sourcePlacement presentation.routes) finalClause =
              metadata.sourceClause.position := by
          rw [finalClauseEq, rawClauseEq]
          exact canonicalClausePosition_normalized
            source sourcePlacement presentation.routes sourceClauseMember
        have sourcePositionMember :=
          refinedClausePosition_mem_sourceVertices
            presentation sourceClauseMember
        rw [← positionEq, canonicalEq]
        exact sourceVertex_in_finalFundamentalSquare presentation
          metadata.sourceClause.position sourcePositionMember
    | complement sourceLiteralIndex sourceLiteral =>
        have valid :=
          PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            baseMetadataMember originEq
        have rawClauseEq :=
          PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            baseMetadataMember originEq
        have canonicalEq :
            PositionedPeriodicCNF.canonicalClausePosition
                (placement sourcePlacement presentation.routes) finalClause =
              routePoint presentation.routes
                ((metadata.sourceClauseIndex, sourceLiteralIndex),
                  sourceLiteral) 2 := by
          rw [finalClauseEq, rawClauseEq]
          exact canonicalClausePosition_complement
            sourcePlacement presentation.routes
            metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
        have pointBounds :=
          (routePoints_one_two_inSquare presentation
            valid.1 valid.2.1).2
        rw [← positionEq, canonicalEq]
        exact finalPositionInFundamentalSquare_of_refinedBounds presentation
          (routePoint presentation.routes
            ((metadata.sourceClauseIndex, sourceLiteralIndex),
              sourceLiteral) 2) pointBounds

/-- The split-and-gauged route family has a complete finite compatibility
certificate with its normalized incidence graph. -/
theorem incidenceDrawing_isCompatible
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
        |>.IsCompatible
          (formula source sourcePlacement presentation.routes).erase.incidenceGraph := by
  simpa [formula, placement, incidenceRoutes] using
    PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_isCompatible
        (rawFormula source sourcePlacement presentation.routes)
        (rawPlacement sourcePlacement presentation.routes)
        freshGauge
        (rawIncidenceRoutes source sourcePlacement presentation.routes)
        (rawPlacement_periodPositive presentation)
        (rawIncidenceDrawing_routesMatch presentation)
        (by simpa [formula, placement] using
          finalIncidenceVertexPositions_nodup presentation)
        (by
          intro position positionMember
          simpa [formula, placement, incidenceRoutes] using
            finalIncidenceVertexPositions_inside presentation
              position positionMember)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
