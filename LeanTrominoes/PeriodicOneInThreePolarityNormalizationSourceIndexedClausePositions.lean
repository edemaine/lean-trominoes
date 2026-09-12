/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteOperationSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertices

/-! # Clause positions selected by source-indexed polarity operations -/

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PeriodicOneInThreePolarityNormalizationPositioned

/-- A main clause retains its refined source origin; either complement
incidence uses the second refined point of the same source route. -/
def SourceIndexedDescriptor.clausePosition {Variable : Type*}
    (descriptor : SourceIndexedDescriptor) (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Cell :=
  match descriptor.operation with
  | .compatible | .incompatible =>
      (source.clauses.getD descriptor.sourceClauseIndex ⟨(0, 0), []⟩).position
  | .complementFresh | .complementOriginal =>
      (refinedRoute routes descriptor.sourceClauseIndex descriptor.sourceLiteralIndex).getD 2 (0, 0)

/-- Every metadata-selected descriptor recovers its gauged canonical clause
position, independently of which literal of that clause is being visited. -/
theorem metadataIndexedDescriptorAt_clausePosition {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (member : metadata ∈ clauseMetadata source sourcePlacement sourceRoutes)
    (literalIndex : Nat) :
    (sourceIndexedDescriptorOf metadata.sourceClauseIndex
      (metadataIndexedDescriptorAt metadata literalIndex)).clausePosition
        (refinedSource source sourcePlacement) sourceRoutes =
      PositionedPeriodicCNF.canonicalClausePosition (placement sourcePlacement sourceRoutes)
        (variableGaugeClause freshGauge metadata.clause) := by
  have sourceMember := formulaClauseMetadata_source_mem
    (rawPositions sourcePlacement sourceRoutes) (refinedSource source sourcePlacement) member
  have sourceLookup := List.mk_mem_zipIdx_iff_getElem?.mp sourceMember
  cases origin : metadata.origin with
  | normalized =>
      have clauseEq := formulaClauseMetadata_normalized_clause_eq
        (rawPositions sourcePlacement sourceRoutes) (refinedSource source sourcePlacement) member origin
      rw [clauseEq, canonicalClausePosition_normalized source sourcePlacement sourceRoutes sourceMember]
      simp only [SourceIndexedDescriptor.clausePosition, sourceIndexedDescriptorOf,
        metadataIndexedDescriptorAt, operationForMetadata, sourceLiteralIndexForMetadata, origin]
      cases selected : metadata.sourceClause.literals[literalIndex]? with
      | none => simp [List.getD_eq_getElem?_getD, sourceLookup]
      | some literal =>
          by_cases compatible : literal.value = PeriodicOneInThreePolarityNormalization.normalizedPolarity literalIndex <;>
            simp [compatible, List.getD_eq_getElem?_getD, sourceLookup]
  | complement sourceLiteralIndex sourceLiteral =>
      have clauseEq := formulaClauseMetadata_complement_clause_eq
        (rawPositions sourcePlacement sourceRoutes) (refinedSource source sourcePlacement) member origin
      rw [clauseEq, canonicalClausePosition_complement]
      simp only [SourceIndexedDescriptor.clausePosition, sourceIndexedDescriptorOf,
        metadataIndexedDescriptorAt, operationForMetadata, sourceLiteralIndexForMetadata, origin]
      by_cases first : literalIndex = 0 <;> simp [first, routePoint]

/-- Canonical clause origins, repeated once for each presented literal. -/
def presentedIncidenceClausePositions {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (sourcePlacement : PeriodicVariablePlacement Variable) : List Cell :=
  source.clauses.flatMap fun clause =>
    List.replicate clause.literals.length (PositionedPeriodicCNF.canonicalClausePosition sourcePlacement clause)

/-- The complete descriptor schedule names the actual canonical clause
origin at every routed incidence, in the output presentation order. -/
theorem exactMetadataRouteBlocks_map_clausePosition {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
      (fun block => block.sourceIndexedDescriptor.clausePosition
        (refinedSource source sourcePlacement) sourceRoutes) =
      presentedIncidenceClausePositions (formula source sourcePlacement sourceRoutes)
        (placement sourcePlacement sourceRoutes) := by
  have clauses : (formula source sourcePlacement sourceRoutes).clauses =
      (clauseMetadata source sourcePlacement sourceRoutes).map
        (fun metadata => variableGaugeClause freshGauge metadata.clause) := by
    unfold formula PositionedPeriodicCNF.variableGauge
    rw [← clauseMetadata_clauses, List.map_map]
    rfl
  unfold exactMetadataRouteBlocks presentedIncidenceClausePositions
  rw [clauses, List.flatMap_map, List.map_flatMap]
  refine (PeriodicCNF.zipIdx_flatMap_fst
    (fun metadata => ((List.range metadata.clause.literals.length).map
      (exactRouteBlockForMetadata metadata)).map
        (fun block => block.sourceIndexedDescriptor.clausePosition
          (refinedSource source sourcePlacement) sourceRoutes))
    (clauseMetadata source sourcePlacement sourceRoutes) 0).trans ?_
  apply List.flatMap_congr
  intro metadata member
  simp only [List.map_map, Function.comp_def, exactRouteBlockForMetadata_sourceIndexedDescriptor]
  rw [show (fun index => (sourceIndexedDescriptorOf metadata.sourceClauseIndex
      (metadataIndexedDescriptorAt metadata index)).clausePosition
        (refinedSource source sourcePlacement) sourceRoutes) =
      (fun _ => PositionedPeriodicCNF.canonicalClausePosition (placement sourcePlacement sourceRoutes)
        (variableGaugeClause freshGauge metadata.clause)) by
      funext index
      exact metadataIndexedDescriptorAt_clausePosition source sourcePlacement sourceRoutes metadata member index]
  simp [variableGaugeClause]

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
