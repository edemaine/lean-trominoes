/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRoutedOriginalOccurrenceProvenance
import LeanTrominoes.PlanarOneInThreeLocalDistinctness

/-!
# Variable-route order under polarity normalization

Original variables retain their global occurrence slots.  At each such slot,
a compatible literal keeps its complete refined route, while an incompatible
literal reaches the original variable through a translated suffix of that
route.  Both cases preserve the terminal direction.  Fresh complement
variables occur at most twice, so they never impose the degree-three cyclic
order condition.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- Dropping the first two points of a route with at least four points does
not change its final directed axis. -/
theorem polylineLastDirection_drop_two
    (points : List Cell) (length : 4 ≤ points.length) :
    AxisDirection.polylineLastDirection (points.drop 2) =
      AxisDirection.polylineLastDirection points := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              cases rest with
              | nil => simp at length
              | cons fourth rest =>
                  simp only [List.drop]
                  rw [AxisDirection.polylineLastDirection_cons_cons_cons
                      first second third (fourth :: rest),
                    AxisDirection.polylineLastDirection_cons_cons_cons
                      second third fourth rest]

/-- Unit subdivision of the scaled source routes preserves variable-side
cyclic order. -/
theorem refinedRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (ordered :
      source.VariableRoutesInOccurrenceOrder presentation.routes) :
    (refinedSource source sourcePlacement).VariableRoutesInOccurrenceOrder
      (refinedRoute presentation.routes) := by
  have scaledOrdered :
      (refinedSource source sourcePlacement).VariableRoutesInOccurrenceOrder
        (scaledSourcePresentation presentation).routes := by
    exact
      (ordered.anchorNormalize sourcePlacement).scaleCoordinates
        refinementFactor refinementFactor_positive
  intro atom first second third firstLookup secondLookup thirdLookup
  have clockwise := scaledOrdered atom first second third
    firstLookup secondLookup thirdLookup
  have directionEq :
      ∀ (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable),
        tagged ∈ PeriodicThreeSATThree.taggedLiterals
          (refinedSource source sourcePlacement).erase →
        AxisDirection.polylineLastDirection
            (refinedRoute presentation.routes tagged.2.1 tagged.2.2) =
          AxisDirection.polylineLastDirection
            ((scaledSourcePresentation presentation).routes
              tagged.2.1 tagged.2.2) := by
    intro tagged taggedMember
    rcases PositionedPeriodicCNF.exists_positionedOccurrence_of_tagged
        (refinedSource source sourcePlacement) taggedMember with
      ⟨clause, clauseMember, literalMember⟩
    apply AxisDirection.polylineLastDirection_unitSubdividePolyline
    · simpa [scaledSourcePresentation_routes, scalePolyline] using
        sourceRoute_length_ge_two_of_refined_members presentation
          clauseMember literalMember
    · exact
        PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
          (sourceRoute_orthogonal_of_refined_members presentation
            clauseMember literalMember)
          refinementFactor_positive
  have firstMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (refinedSource source sourcePlacement).erase atom .first
      first firstLookup).1
  have secondMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (refinedSource source sourcePlacement).erase atom .second
      second secondLookup).1
  have thirdMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (refinedSource source sourcePlacement).erase atom .third
      third thirdLookup).1
  rw [directionEq first firstMember,
    directionEq second secondMember,
    directionEq third thirdMember]
  exact clockwise

/-- Membership in the enriched pair exposes the exact metadata lookup,
output literal, and retained refined source clause. -/
theorem rawOriginalOccurrencePair_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    {pair : RawOriginalOccurrencePair Variable}
    (pairMember :
      pair ∈ rawOriginalOccurrencePairs
        source sourcePlacement routes atom) :
    (clauseMetadata source sourcePlacement routes)[pair.1.1.2.1]? =
        some pair.1.2 ∧
      (pair.1.1.1, pair.1.1.2.2) ∈ pair.1.2.clause.literals.zipIdx ∧
      pair.1.1.1.atom = Sum.inl atom ∧
      (pair.1.2.sourceClause, pair.1.2.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx := by
  have metadataOccurrenceMember :
      pair.1 ∈ rawOriginalMetadataOccurrences
        source sourcePlacement routes atom := by
    have mappedMember :
        pair.1 ∈
          (rawOriginalOccurrencePairs source sourcePlacement routes atom).map
            Prod.fst :=
      List.mem_map_of_mem pairMember
    rw [rawOriginalOccurrencePairs_map_metadata] at mappedMember
    exact mappedMember
  have selected := List.mem_filter.mp metadataOccurrenceMember
  have outputAtom := of_decide_eq_true selected.2
  simp only [taggedMetadataLiteralsFrom, List.mem_flatMap,
    List.mem_map] at selected
  rcases selected.1 with
    ⟨taggedMetadata, taggedMetadataMember,
      taggedLiteral, taggedLiteralMember, pairEq⟩
  have metadataMember :
      taggedMetadata.1 ∈ clauseMetadata source sourcePlacement routes :=
    List.fst_mem_of_mem_zipIdx taggedMetadataMember
  have metadataLookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMetadataMember
  have outputAtom' : taggedLiteral.1.atom = Sum.inl atom :=
    (congrArg (fun value => value.1.1.atom) pairEq).trans outputAtom
  rw [← pairEq]
  exact ⟨metadataLookup, taggedLiteralMember, outputAtom',
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement routes)
      (refinedSource source sourcePlacement) metadataMember⟩

/-- Anchor normalization preserves per-clause atom distinctness. -/
theorem allAtomsNodup_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (distinct : source.AllAtomsNodup) :
    (source.anchorNormalize placement).AllAtomsNodup := by
  intro normalizedClause normalizedMember
  unfold PositionedPeriodicCNF.anchorNormalize at normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨sourceClause, sourceMember, rfl⟩
  have sourceDistinct := distinct sourceClause sourceMember
  unfold PositionedPeriodicClause.AtomsNodup at sourceDistinct ⊢
  simpa [PeriodicClause.anchorNormalize, List.map_map,
    Function.comp_def] using sourceDistinct

/-- The refined source retains per-clause atom distinctness. -/
theorem allAtomsNodup_refinedSource
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (distinct : source.AllAtomsNodup) :
    (refinedSource source placement).AllAtomsNodup := by
  exact (allAtomsNodup_anchorNormalize placement distinct).scale
    refinementFactor

/-- Two literals of one atom-distinct source clause are equal as soon as
their atoms agree. -/
private theorem sourceLiteral_eq_of_atom_eq
    {Variable : Type*} [DecidableEq Variable]
    {sourceClause : PositionedPeriodicClause Variable}
    (distinct : sourceClause.AtomsNodup)
    {first second : PeriodicLiteral Variable}
    {firstIndex secondIndex : Nat}
    (firstMember : (first, firstIndex) ∈ sourceClause.literals.zipIdx)
    (secondMember : (second, secondIndex) ∈ sourceClause.literals.zipIdx)
    (atomEq : first.atom = second.atom) :
    first = second ∧ firstIndex = secondIndex := by
  have literalsNodup : sourceClause.literals.Nodup :=
    distinct.of_map PeriodicLiteral.atom
  have firstEqSecond : first = second := by
    apply
      ((List.nodup_map_iff_inj_on literalsNodup).mp distinct)
        first (List.fst_mem_of_mem_zipIdx firstMember)
        second (List.fst_mem_of_mem_zipIdx secondMember)
    exact atomEq
  have firstParts := List.mem_zipIdx' firstMember
  have secondParts := List.mem_zipIdx' secondMember
  have indexEq : firstIndex = secondIndex := by
    apply (literalsNodup.getElem_inj_iff
      (hi := firstParts.1) (hj := secondParts.1)).mp
    rw [← firstParts.2, ← secondParts.2, firstEqSecond]
  exact ⟨firstEqSecond, indexEq⟩

private theorem value_eq_of_mem_zipIdx_same_index
    {Value : Type*} {values : List Value}
    {first second : Value} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- Every paired raw route of an embedded original variable retains the final
direction of its paired refined source route. -/
theorem rawOriginalOccurrencePair_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (sourceDistinct : source.AllAtomsNodup)
    (atom : Variable)
    {pair : RawOriginalOccurrencePair Variable}
    (pairMember :
      pair ∈ rawOriginalOccurrencePairs
        source sourcePlacement presentation.routes atom) :
    AxisDirection.polylineLastDirection
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          pair.1.1.2.1 pair.1.1.2.2) =
      AxisDirection.polylineLastDirection
        (refinedRoute presentation.routes pair.2.2.1 pair.2.2.2) := by
  rcases rawOriginalOccurrencePair_data source sourcePlacement
      presentation.routes atom pairMember with
    ⟨metadataLookup, outputLiteralMember, outputAtom,
      metadataSourceMember⟩
  have sourceOccurrenceMember :
      pair.2 ∈ PeriodicOneInThreeToThreeDM.occurrencesOf
        (refinedSource source sourcePlacement).erase atom := by
    have mappedMember :
        pair.2 ∈
          (rawOriginalOccurrencePairs source sourcePlacement
            presentation.routes atom).map Prod.snd :=
      List.mem_map_of_mem pairMember
    rw [rawOriginalOccurrencePairs_map_source] at mappedMember
    exact mappedMember
  have sourceTaggedInfo := List.mem_filter.mp sourceOccurrenceMember
  have sourceAtom : pair.2.1.atom = atom := of_decide_eq_true sourceTaggedInfo.2
  rcases PositionedPeriodicCNF.exists_positionedOccurrence_of_tagged
      (refinedSource source sourcePlacement) sourceTaggedInfo.1 with
    ⟨pairedClause, pairedClauseMember, pairedLiteralMember⟩
  have sourceClauseIndexEq :=
    rawOriginalOccurrencePair_sourceClauseIndex
      source sourcePlacement presentation.routes atom pairMember
  have sourceClauseEq : pair.1.2.sourceClause = pairedClause :=
    value_eq_of_mem_zipIdx_same_index metadataSourceMember
      (by simpa [sourceClauseIndexEq] using pairedClauseMember)
  have refinedDistinct :=
    allAtomsNodup_refinedSource sourcePlacement sourceDistinct
  have metadataMember :
      pair.1.2 ∈ clauseMetadata
        source sourcePlacement presentation.routes := by
    exact List.mem_iff_getElem?.mpr
      ⟨pair.1.1.2.1, metadataLookup⟩
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement presentation.routes pair.1.2
    pair.1.1.2.1 pair.1.1.2.2 metadataLookup]
  cases originEq : pair.1.2.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
      have normalizedLiteralMember :
          (pair.1.1.1, pair.1.1.2.2) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
              pair.1.2.sourceClauseIndex
              pair.1.2.sourceClause).literals.zipIdx := by
        rw [← normalizedClauseEq]
        exact outputLiteralMember
      have normalizedLiteralLookup :
          (PeriodicOneInThreePolarityNormalization.normalizeClause
            pair.1.2.sourceClauseIndex pair.1.2.sourceClause.literals
            )[pair.1.1.2.2]? = some pair.1.1.1 := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause]
          using (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
      rw [PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?]
        at normalizedLiteralLookup
      rcases Option.map_eq_some_iff.mp normalizedLiteralLookup with
        ⟨sourceLiteral, sourceLiteralLookup, normalizedLiteralEq⟩
      have sourceLiteralMember :
          (sourceLiteral, pair.1.1.2.2) ∈
            pair.1.2.sourceClause.literals.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
      by_cases compatible :
          sourceLiteral.value =
            PeriodicOneInThreePolarityNormalization.normalizedPolarity
              pair.1.1.2.2
      · have sourceLiteralAtom : sourceLiteral.atom = atom := by
          rw [PeriodicOneInThreePolarityNormalization.normalizeLiteral,
            if_pos compatible] at normalizedLiteralEq
          have atomEq := congrArg PeriodicLiteral.atom normalizedLiteralEq
          simpa [PeriodicOneInThreePolarityNormalization.liftLiteral,
            outputAtom] using atomEq
        have pairedLiteralMember' :
            (pair.2.1, pair.2.2.2) ∈
              pair.1.2.sourceClause.literals.zipIdx := by
          rw [sourceClauseEq]
          exact pairedLiteralMember
        have literalParts := sourceLiteral_eq_of_atom_eq
          (refinedDistinct pair.1.2.sourceClause
            (List.fst_mem_of_mem_zipIdx metadataSourceMember))
          sourceLiteralMember pairedLiteralMember'
          (sourceLiteralAtom.trans sourceAtom.symm)
        rw [rawRouteForMetadata_normalized_compatible
          sourcePlacement presentation.routes pair.1.2 sourceLiteral
          pair.1.1.2.2 originEq sourceLiteralLookup compatible]
        rw [literalParts.2, sourceClauseIndexEq]
      · rw [PeriodicOneInThreePolarityNormalization.normalizeLiteral,
          if_neg compatible] at normalizedLiteralEq
        have atomEq := congrArg PeriodicLiteral.atom normalizedLiteralEq
        simp [PeriodicOneInThreePolarityNormalization.complementLiteral,
          outputAtom] at atomEq
  | complement sourceLiteralIndex sourceLiteral =>
      have complementValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
      have complementLiteralMember :
          (pair.1.1.1, pair.1.1.2.2) ∈
            (positionedComplementClause
              (rawPositions sourcePlacement presentation.routes)
              pair.1.2.sourceClauseIndex sourceLiteralIndex
              sourceLiteral).literals.zipIdx := by
        rw [← complementClauseEq]
        exact outputLiteralMember
      have outputIndexLt : pair.1.1.2.2 < 2 := by
        simpa [positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause] using
          List.snd_lt_of_mem_zipIdx complementLiteralMember
      have outputIndexCases : pair.1.1.2.2 = 0 ∨ pair.1.1.2.2 = 1 := by
        omega
      rcases outputIndexCases with outputIndexEq | outputIndexEq
      · have outputLookup :=
          (List.mem_zipIdx_iff_getElem?).mp complementLiteralMember
        rw [outputIndexEq] at outputLookup
        simp [positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause,
          PeriodicOneInThreePolarityNormalization.complementFalseLiteral]
          at outputLookup
        have atomEq := congrArg PeriodicLiteral.atom outputLookup
        simp [outputAtom] at atomEq
      · have outputLookup :=
          (List.mem_zipIdx_iff_getElem?).mp complementLiteralMember
        rw [outputIndexEq] at outputLookup
        simp [positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause,
          PeriodicOneInThreePolarityNormalization.originalFalseLiteral]
          at outputLookup
        have sourceLiteralAtom : sourceLiteral.atom = atom := by
          have atomEq := congrArg PeriodicLiteral.atom outputLookup
          simpa [outputAtom] using atomEq
        have pairedLiteralMember' :
            (pair.2.1, pair.2.2.2) ∈
              pair.1.2.sourceClause.literals.zipIdx := by
          rw [sourceClauseEq]
          exact pairedLiteralMember
        have literalParts := sourceLiteral_eq_of_atom_eq
          (refinedDistinct pair.1.2.sourceClause
            (List.fst_mem_of_mem_zipIdx metadataSourceMember))
          complementValid.2.1 pairedLiteralMember'
          (sourceLiteralAtom.trans sourceAtom.symm)
        rw [outputIndexEq]
        rw [rawRouteForMetadata_complement_original
          sourcePlacement presentation.routes pair.1.2 sourceLiteral
          sourceLiteralIndex originEq]
        rw [AxisDirection.polylineLastDirection_translatePolyline]
        rw [polylineLastDirection_drop_two _
          (refinedRoute_length_ge_four_of_members presentation
            metadataSourceMember complementValid.2.1)]
        rw [literalParts.2, sourceClauseIndexEq]

/-- Before the final gauge, original variables inherit their refined source
order and fresh variables are vacuous because they have degree at most two. -/
theorem rawIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (sourceDistinct : source.AllAtomsNodup)
    (ordered :
      source.VariableRoutesInOccurrenceOrder presentation.routes) :
    (rawFormula source sourcePlacement presentation.routes)
      |>.VariableRoutesInOccurrenceOrder
        (rawIncidenceRoutes source sourcePlacement presentation.routes) := by
  have refinedOrdered :=
    refinedRoutes_variableRoutesInOccurrenceOrder presentation ordered
  intro outputAtom first second third
    firstLookup secondLookup thirdLookup
  cases outputAtom with
  | inl atom =>
      rcases exists_metadata_source_occurrenceAt
          source sourcePlacement presentation.routes atom .first
          first firstLookup with
        ⟨firstMetadata, sourceFirst, sourceFirstLookup, firstPair⟩
      rcases exists_metadata_source_occurrenceAt
          source sourcePlacement presentation.routes atom .second
          second secondLookup with
        ⟨secondMetadata, sourceSecond, sourceSecondLookup, secondPair⟩
      rcases exists_metadata_source_occurrenceAt
          source sourcePlacement presentation.routes atom .third
          third thirdLookup with
        ⟨thirdMetadata, sourceThird, sourceThirdLookup, thirdPair⟩
      have clockwise := refinedOrdered atom sourceFirst sourceSecond sourceThird
        sourceFirstLookup sourceSecondLookup sourceThirdLookup
      rw [rawOriginalOccurrencePair_lastDirection
          presentation sourceDistinct atom firstPair,
        rawOriginalOccurrencePair_lastDirection
          presentation sourceDistinct atom secondPair,
        rawOriginalOccurrencePair_lastDirection
          presentation sourceDistinct atom thirdPair]
      exact clockwise
  | inr fresh =>
      have logicalThird :
          PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
              (PeriodicOneInThreePolarityNormalization.formula
                (refinedSource source sourcePlacement).erase)
              (Sum.inr fresh) .third = some third := by
        simpa [rawFormula] using thirdLookup
      change
        PeriodicOneInThreeToThreeDM.occurrenceAt
            (PeriodicOneInThreePolarityNormalization.formula
              (refinedSource source sourcePlacement).erase)
            (Sum.inr fresh) .third = some third at logicalThird
      have lower :=
        PeriodicOneInThreeToThreeDM.three_le_variableOccurrences_count_of_occurrenceAt_third
          (PeriodicOneInThreePolarityNormalization.formula
            (refinedSource source sourcePlacement).erase)
          (Sum.inr fresh) third logicalThird
      rcases fresh with ⟨⟨clauseIndex, literalIndex⟩, literal⟩
      have upper :=
        PeriodicOneInThreePolarityNormalization.formula_variableOccurrences_count_auxiliary_le_two
          (refinedSource source sourcePlacement).erase
          clauseIndex literalIndex literal
      have countInstanceEq :
          @List.count (PolarityNormalizedVariable Variable)
              instBEqOfDecidableEq
              (Sum.inr ((clauseIndex, literalIndex), literal))
              (PeriodicCNF.variableOccurrences
                (PeriodicOneInThreePolarityNormalization.formula
                  (refinedSource source sourcePlacement).erase)) =
            @List.count (PolarityNormalizedVariable Variable)
              Sum.instBEq
              (Sum.inr ((clauseIndex, literalIndex), literal))
              (PeriodicCNF.variableOccurrences
                (PeriodicOneInThreePolarityNormalization.formula
                  (refinedSource source sourcePlacement).erase)) := by
        unfold List.count
        congr 1
        funext head
        by_cases same :
            head = Sum.inr ((clauseIndex, literalIndex), literal) <;>
          simp [same]
      rw [countInstanceEq] at lower
      omega

/-- The final fresh-variable gauge preserves variable-side occurrence order
for the routed polarity-normalized formula. -/
theorem incidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (sourceDistinct : source.AllAtomsNodup)
    (ordered :
      source.VariableRoutesInOccurrenceOrder presentation.routes) :
    (formula source sourcePlacement presentation.routes)
      |>.VariableRoutesInOccurrenceOrder
        (incidenceRoutes source sourcePlacement presentation.routes) := by
  exact
    (rawIncidenceRoutes_variableRoutesInOccurrenceOrder
      presentation sourceDistinct ordered)
      |>.variableGaugeCanonicalIncidenceRoutes freshGauge

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
