/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRefinedSourceMembership
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteDirectionData
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertexInjectivity

/-! # Compact direction blocks through routed polarity normalization -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open Gadget

universe u

/-- The four stream operations applied to one compact source-route word by
routed polarity normalization. -/
inductive RouteDirectionBlock (SourceBlock : Type u) where
  | compatible (source : SourceBlock)
  | incompatible (source : SourceBlock)
  | complementFresh (source : SourceBlock)
  | complementOriginal (source : SourceBlock)

/-- Interpret a compact polarity route block from the underlying source-word
interpreter. -/
def RouteDirectionBlock.directions {SourceBlock : Type u}
    (sourceDirections : SourceBlock → List AxisDirection) :
    RouteDirectionBlock SourceBlock → List AxisDirection
  | .compatible source =>
      repeatDirections refinementFactor (sourceDirections source)
  | .incompatible source =>
      (repeatDirections refinementFactor (sourceDirections source)).take 1
  | .complementFresh source =>
      reverseDirections
        (((repeatDirections refinementFactor
          (sourceDirections source)).drop 1).take 1)
  | .complementOriginal source =>
      (repeatDirections refinementFactor (sourceDirections source)).drop 2

/-- If every genuine source occurrence has a compact direction block and
the usual route geometry, then every routed polarity-normalized occurrence
has one of the four corresponding compact stream forms. -/
theorem route_directionBlock_of_members
    {Variable SourceBlock : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceDirections : SourceBlock → List AxisDirection)
    (sourceBlocks :
      ∀ {sourceClause : PositionedPeriodicClause Variable}
          {sourceClauseIndex : Nat},
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ {sourceLiteral : PeriodicLiteral Variable}
            {sourceLiteralIndex : Nat},
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ block : SourceBlock,
            unitSubdivisionDirections
                (sourceRoutes sourceClauseIndex sourceLiteralIndex) =
              sourceDirections block)
    (sourceGeometry :
      ∀ {sourceClause : PositionedPeriodicClause Variable}
          {sourceClauseIndex : Nat},
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ {sourceLiteral : PeriodicLiteral Variable}
            {sourceLiteralIndex : Nat},
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          2 ≤ (sourceRoutes sourceClauseIndex sourceLiteralIndex).length ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    {outputClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (formula source sourcePlacement sourceRoutes).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral (PolarityNormalizedVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈
        outputClause.literals.zipIdx) :
    ∃ block : RouteDirectionBlock SourceBlock,
      unitSubdivisionDirections
          (incidenceRoutes source sourcePlacement sourceRoutes
            outputClauseIndex outputLiteralIndex) =
        block.directions sourceDirections := by
  rcases exists_metadata_of_final_clause_member
      source sourcePlacement sourceRoutes outputClauseMember with
    ⟨metadata, metadataLookup, metadataMember,
      refinedSourceClauseMember, outputClauseEq⟩
  have baseMetadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement) := by
    simpa only [clauseMetadata] using metadataMember
  have gaugedOutputLiteralLookup :
      (metadata.clause.literals.variableGauge freshGauge)[outputLiteralIndex]? =
        some outputLiteral := by
    rw [outputClauseEq] at outputLiteralMember
    exact (List.mem_zipIdx_iff_getElem?).mp outputLiteralMember
  rw [PeriodicClause.variableGauge, List.getElem?_map] at gaugedOutputLiteralLookup
  rcases Option.map_eq_some_iff.mp gaugedOutputLiteralLookup with
    ⟨rawOutputLiteral, rawOutputLiteralLookup,
      _gaugedOutputLiteralEq⟩
  have rawOutputLiteralMember :
      (rawOutputLiteral, outputLiteralIndex) ∈
        metadata.clause.literals.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr rawOutputLiteralLookup
  have rawClauseLookup :
      (rawFormula source sourcePlacement sourceRoutes).clauses[
          outputClauseIndex]? = some metadata.clause := by
    rw [← clauseMetadata_clauses]
    rw [List.getElem?_map, metadataLookup]
    rfl
  have rawClauseMember :
      (metadata.clause, outputClauseIndex) ∈
        (rawFormula source sourcePlacement sourceRoutes).clauses.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr rawClauseLookup
  have outputDirections :=
    incidenceRoutes_directionWord_of_raw_clause_mem
      source sourcePlacement sourceRoutes rawClauseMember
      (literalIndex := outputLiteralIndex)
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement sourceRoutes metadata
    outputClauseIndex outputLiteralIndex metadataLookup] at outputDirections
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement)
          baseMetadataMember originEq
      have normalizedLiteralMember :
          (rawOutputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
              metadata.sourceClauseIndex metadata.sourceClause).literals.zipIdx := by
        rw [← normalizedClauseEq]
        exact rawOutputLiteralMember
      have normalizedLiteralLookup :
          (PeriodicOneInThreePolarityNormalization.normalizeClause
            metadata.sourceClauseIndex metadata.sourceClause.literals)[
              outputLiteralIndex]? = some rawOutputLiteral := by
        simpa [
          PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause]
          using (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
      rw [PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?]
          at normalizedLiteralLookup
      rcases Option.map_eq_some_iff.mp normalizedLiteralLookup with
        ⟨refinedSourceLiteral, refinedSourceLiteralLookup,
          _rawOutputLiteralEq⟩
      have refinedSourceLiteralMember :
          (refinedSourceLiteral, outputLiteralIndex) ∈
            metadata.sourceClause.literals.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr refinedSourceLiteralLookup
      rcases exists_source_members_of_refinedSource_members
          source sourcePlacement refinedSourceClauseMember
          refinedSourceLiteralMember with
        ⟨sourceClause, sourceLiteral,
          sourceClauseMember, sourceLiteralMember⟩
      rcases sourceBlocks sourceClauseMember sourceLiteralMember with
        ⟨sourceBlock, sourceWord⟩
      have geometry := sourceGeometry
        sourceClauseMember sourceLiteralMember
      by_cases compatible :
          refinedSourceLiteral.value =
            PeriodicOneInThreePolarityNormalization.normalizedPolarity
              outputLiteralIndex
      · have rawDirections :=
          rawRouteForMetadata_normalized_compatible_directionWord
            sourcePlacement sourceRoutes metadata refinedSourceLiteral
            outputLiteralIndex originEq refinedSourceLiteralLookup
            compatible geometry.2
        rw [sourceWord] at rawDirections
        refine ⟨.compatible sourceBlock, ?_⟩
        exact outputDirections.trans (by
          simpa [RouteDirectionBlock.directions] using rawDirections)
      · have rawDirections :=
          rawRouteForMetadata_normalized_incompatible_directionWord
            sourcePlacement sourceRoutes metadata refinedSourceLiteral
            outputLiteralIndex originEq refinedSourceLiteralLookup
            compatible geometry.2
        rw [sourceWord] at rawDirections
        refine ⟨.incompatible sourceBlock, ?_⟩
        exact outputDirections.trans (by
          simpa [RouteDirectionBlock.directions] using rawDirections)
  | complement sourceLiteralIndex refinedSourceLiteral =>
      have complementValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement)
          baseMetadataMember originEq
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement)
          baseMetadataMember originEq
      rcases exists_source_members_of_refinedSource_members
          source sourcePlacement complementValid.1 complementValid.2.1 with
        ⟨sourceClause, sourceLiteral,
          sourceClauseMember, sourceLiteralMember⟩
      rcases sourceBlocks sourceClauseMember sourceLiteralMember with
        ⟨sourceBlock, sourceWord⟩
      have geometry := sourceGeometry
        sourceClauseMember sourceLiteralMember
      have complementLiteralMember :
          (rawOutputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
              (rawPositions sourcePlacement sourceRoutes)
              metadata.sourceClauseIndex sourceLiteralIndex
              refinedSourceLiteral).literals.zipIdx := by
        rw [← complementClauseEq]
        exact rawOutputLiteralMember
      have outputLiteralIndexLt : outputLiteralIndex < 2 := by
        have indexLt := List.snd_lt_of_mem_zipIdx complementLiteralMember
        simpa [
          PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause] using
          indexLt
      have outputIndexCases :
          outputLiteralIndex = 0 ∨ outputLiteralIndex = 1 := by
        omega
      rcases outputIndexCases with outputIndexEq | outputIndexEq
      · subst outputLiteralIndex
        have rawDirections :=
          rawRouteForMetadata_complement_fresh_directionWord
            sourcePlacement sourceRoutes metadata refinedSourceLiteral
            sourceLiteralIndex originEq geometry.1 geometry.2
        rw [sourceWord] at rawDirections
        refine ⟨.complementFresh sourceBlock, ?_⟩
        exact outputDirections.trans (by
          simpa [RouteDirectionBlock.directions] using rawDirections)
      · subst outputLiteralIndex
        have rawDirections :=
          rawRouteForMetadata_complement_original_directionWord
            sourcePlacement sourceRoutes metadata refinedSourceLiteral
            sourceLiteralIndex originEq geometry.2
        rw [sourceWord] at rawDirections
        refine ⟨.complementOriginal sourceBlock, ?_⟩
        exact outputDirections.trans (by
          simpa [RouteDirectionBlock.directions] using rawDirections)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
