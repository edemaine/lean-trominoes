import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRawRouteDescriptors
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRefinedRouteBounds

/-!
# Halo bounds for raw polarity-normalization routes

Each raw split route is a translated fragment of one complete refined source
route.  Reversing and rebasing the raw incidence cancels that canonical
whole-period translation, so every resulting point belongs to the rebased
complete refined route and inherits its open halo bound.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

namespace RawRouteDescriptor

/-- The output clause selected by a descriptor is exactly its metadata
clause. -/
theorem outputClause_eq_metadataClause
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence)
    {outputClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    (outputClauseMember :
      (outputClause, taggedIncidence.1.clauseIndex) ∈
        (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx) :
    outputClause = descriptor.metadata.clause := by
  have outputLookup :=
    (List.mem_zipIdx_iff_getElem?).mp outputClauseMember
  have metadataLookup :
      ((clauseMetadata source sourcePlacement presentation.routes).map
        PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata.clause)[
          taggedIncidence.1.clauseIndex]? =
        some descriptor.metadata.clause := by
    simp only [List.getElem?_map, descriptor.metadataLookup,
      Option.map_some]
  rw [clauseMetadata_clauses] at metadataLookup
  exact Option.some.inj (outputLookup.symm.trans metadataLookup)

/-- The raw incidence rebase followed by the descriptor's canonical route
shift equals the rebase of its complete refined source incidence. -/
theorem rebase_add_latticeShift
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    Cell.add
        ((refinedIncidenceDrawing presentation).periodTranslation
          descriptor.latticeShift)
        ((rawPlacement sourcePlacement presentation.routes).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor taggedIncidence.1.clause)
            taggedIncidence.1.literal.offset)) =
      (refinedPlacement sourcePlacement).translation
        (Cell.sub
          (PeriodicCNF.clauseAnchor descriptor.metadata.sourceClause.literals)
          descriptor.sourceLiteral.offset) := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, incidenceEq⟩
  have outputClauseEq : outputClause = descriptor.metadata.clause :=
    descriptor.outputClause_eq_metadataClause outputClauseMember
  subst outputClause
  rw [incidenceEq]
  change
    Cell.add
        ((refinedIncidenceDrawing presentation).periodTranslation
          descriptor.latticeShift)
        ((rawPlacement sourcePlacement presentation.routes).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor descriptor.metadata.clause.literals)
            outputLiteral.offset)) =
      (refinedPlacement sourcePlacement).translation
        (Cell.sub
          (PeriodicCNF.clauseAnchor descriptor.metadata.sourceClause.literals)
          descriptor.sourceLiteral.offset)
  have metadataMember :
      descriptor.metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    have rawMember : descriptor.metadata ∈
        clauseMetadata source sourcePlacement presentation.routes := by
      rcases List.getElem?_eq_some_iff.mp descriptor.metadataLookup with
        ⟨metadataIndexLt, metadataAt⟩
      rw [← metadataAt]
      exact List.getElem_mem metadataIndexLt
    simpa only [clauseMetadata] using rawMember
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement descriptor.sourceClauseMember
  rcases descriptor.shape.classifyWithShift with
      wholeCase | prefixCase | middleCase | suffixCase
  · rcases wholeCase with
      ⟨_fragmentEq, latticeShiftEq, originEq, sourceIndex, compatible⟩
    rw [latticeShiftEq]
    have normalizedClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
    have normalizedLiteralMember :
        (outputLiteral, descriptor.sourceLiteralIndex) ∈
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            descriptor.metadata.sourceClauseIndex
            descriptor.metadata.sourceClause).literals.zipIdx := by
      rw [sourceIndex, ← normalizedClauseEq]
      exact outputLiteralMember
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp descriptor.sourceLiteralMember
    have outputOffsetEq :
        outputLiteral.offset = descriptor.sourceLiteral.offset := by
      rw [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
        PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?,
        sourceLiteralLookup] at outputLiteralLookup
      have outputLiteralEq :
          PeriodicOneInThreePolarityNormalization.normalizeLiteral
              descriptor.metadata.sourceClauseIndex
              descriptor.sourceLiteralIndex descriptor.sourceLiteral =
            outputLiteral := by
        simpa using Option.some.inj outputLiteralLookup
      rw [← outputLiteralEq]
      exact PeriodicOneInThreePolarityNormalization.normalizeLiteral_offset
        _ _ _
    simp [normalizedClauseEq,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      outputOffsetEq, sourceAnchor, rawPlacement,
      refinedIncidenceDrawing, PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale]
  · rcases prefixCase with
      ⟨_fragmentEq, latticeShiftEq, originEq, sourceIndex, incompatible⟩
    rw [latticeShiftEq]
    have normalizedClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
    have normalizedLiteralMember :
        (outputLiteral, descriptor.sourceLiteralIndex) ∈
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            descriptor.metadata.sourceClauseIndex
            descriptor.metadata.sourceClause).literals.zipIdx := by
      rw [sourceIndex, ← normalizedClauseEq]
      exact outputLiteralMember
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp descriptor.sourceLiteralMember
    have outputOffsetEq :
        outputLiteral.offset = descriptor.sourceLiteral.offset := by
      rw [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
        PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?,
        sourceLiteralLookup] at outputLiteralLookup
      have outputLiteralEq :
          PeriodicOneInThreePolarityNormalization.normalizeLiteral
              descriptor.metadata.sourceClauseIndex
              descriptor.sourceLiteralIndex descriptor.sourceLiteral =
            outputLiteral := by
        simpa using Option.some.inj outputLiteralLookup
      rw [← outputLiteralEq]
      exact PeriodicOneInThreePolarityNormalization.normalizeLiteral_offset
        _ _ _
    simp [normalizedClauseEq,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      outputOffsetEq, sourceAnchor, rawPlacement,
      refinedIncidenceDrawing, PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale]
  · rcases middleCase with
      ⟨_fragmentEq, latticeShiftEq, originEq, outputIndex, incompatible⟩
    rw [latticeShiftEq]
    have complementClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp outputLiteralMember
    have outputOffsetEq :
        outputLiteral.offset = descriptor.sourceLiteral.offset := by
      rw [outputIndex, complementClauseEq] at outputLiteralLookup
      have outputLiteralEq :
          PeriodicOneInThreePolarityNormalization.complementFalseLiteral
              descriptor.metadata.sourceClauseIndex
              descriptor.sourceLiteralIndex descriptor.sourceLiteral =
            outputLiteral := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause]
          using outputLiteralLookup
      rw [← outputLiteralEq]
      rfl
    have shiftEq :
        (refinedIncidenceDrawing presentation).periodTranslation
            (complementLatticeShift descriptor.sourceLiteral) =
          complementCanonicalShift sourcePlacement
            descriptor.sourceLiteral := by
      simpa [refinedIncidenceDrawing] using
        (complementCanonicalShift_eq_periodTranslation
          presentation descriptor.sourceLiteral).symm
    rw [shiftEq]
    simp [complementClauseEq,
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
      clauseAnchor_complementClause, outputOffsetEq, sourceAnchor,
      complementCanonicalShift, rawPlacement,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub,
      Cell.scale]
  · rcases suffixCase with
      ⟨_fragmentEq, latticeShiftEq, originEq, outputIndex, incompatible⟩
    rw [latticeShiftEq]
    have complementClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp outputLiteralMember
    have outputOffsetEq :
        outputLiteral.offset = descriptor.sourceLiteral.offset := by
      rw [outputIndex, complementClauseEq] at outputLiteralLookup
      have outputLiteralEq :
          PeriodicOneInThreePolarityNormalization.originalFalseLiteral
              descriptor.sourceLiteral = outputLiteral := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause]
          using outputLiteralLookup
      rw [← outputLiteralEq]
      rfl
    have shiftEq :
        (refinedIncidenceDrawing presentation).periodTranslation
            (complementLatticeShift descriptor.sourceLiteral) =
          complementCanonicalShift sourcePlacement
            descriptor.sourceLiteral := by
      simpa [refinedIncidenceDrawing] using
        (complementCanonicalShift_eq_periodTranslation
          presentation descriptor.sourceLiteral).symm
    rw [shiftEq]
    simp [complementClauseEq,
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
      clauseAnchor_complementClause, outputOffsetEq, sourceAnchor,
      complementCanonicalShift, rawPlacement,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub,
      Cell.scale]

/-- A descriptor identifies the raw reversed-and-rebased route exactly with
the correspondingly rebased refined source fragment. -/
theorem rebasedRouteEq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    PeriodicOrthocrossing.translatePolyline
        ((rawPlacement sourcePlacement presentation.routes).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor taggedIncidence.1.clause)
            taggedIncidence.1.literal.offset))
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          taggedIncidence.1.clauseIndex
          taggedIncidence.1.literalIndex).reverse =
      PeriodicOrthocrossing.translatePolyline
        ((refinedPlacement sourcePlacement).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor
              descriptor.metadata.sourceClause.literals)
            descriptor.sourceLiteral.offset))
        (descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex)).reverse := by
  rw [descriptor.routeEq]
  rw [show
    (PeriodicOrthocrossing.translatePolyline
        ((refinedIncidenceDrawing presentation).periodTranslation
          descriptor.latticeShift)
        (descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex))).reverse =
      PeriodicOrthocrossing.translatePolyline
        ((refinedIncidenceDrawing presentation).periodTranslation
          descriptor.latticeShift)
        (descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex)).reverse by
    simp [PeriodicOrthocrossing.translatePolyline]]
  rw [PeriodicOrthocrossing.translatePolyline_add]
  rw [descriptor.rebase_add_latticeShift taggedIncidenceMember]

/-- Every point of a raw reversed-and-rebased route is a point of the
complete refined reversed-and-rebased source route selected by its
descriptor. -/
theorem rebasedPoint_mem_refinedVariableToClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (descriptor : RawRouteDescriptor presentation taggedIncidence)
    {point : Cell}
    (pointMember :
      point ∈ PeriodicOrthocrossing.translatePolyline
        ((rawPlacement sourcePlacement presentation.routes).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor taggedIncidence.1.clause)
            taggedIncidence.1.literal.offset))
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          taggedIncidence.1.clauseIndex
          taggedIncidence.1.literalIndex).reverse) :
    point ∈
      ((refinedContinuousPlanarPresentation presentation)
        |>.toPlanarIncidencePresentation
        |>.variableToClauseRoute descriptor.sourceIncidence) := by
  rw [descriptor.rebasedRouteEq taggedIncidenceMember] at pointMember
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨fragmentPoint, fragmentPointMember, rfl⟩
  apply List.mem_map.mpr
  refine ⟨fragmentPoint, ?_, rfl⟩
  change
    fragmentPoint ∈
      (refinedRoute presentation.routes
        descriptor.metadata.sourceClauseIndex
        descriptor.sourceLiteralIndex).reverse
  rw [List.mem_reverse]
  apply descriptor.fragment.select_subset _ descriptor.sourceRoute_length_ge_four
  simpa using fragmentPointMember

/-- The two near-clause fragment kinds use only refined points zero, one,
and two, all of which remain inside the final normalized fundamental
square. -/
theorem nearClauseFragment_pointInsideFinalExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence)
    (nearClause :
      descriptor.fragment = .prefix ∨ descriptor.fragment = .middle)
    {point : Cell}
    (pointMember :
      point ∈ descriptor.fragment.select
        (refinedRoute presentation.routes
          descriptor.metadata.sourceClauseIndex
          descriptor.sourceLiteralIndex)) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.PositionInExpandedSquare point := by
  let route := refinedRoute presentation.routes
    descriptor.metadata.sourceClauseIndex descriptor.sourceLiteralIndex
  have routeLength : 4 ≤ route.length := descriptor.sourceRoute_length_ge_four
  have pointCases := descriptor.fragment.select_mem_getD_zero_one_two
    route routeLength nearClause pointMember
  have routeEndpoints :=
    (refinedRouteFamily presentation).endpoints
      descriptor.metadata.sourceClause
      descriptor.metadata.sourceClauseIndex descriptor.sourceClauseMember
      descriptor.sourceLiteral descriptor.sourceLiteralIndex
      descriptor.sourceLiteralMember
  rw [refinedRouteFamily_routes] at routeEndpoints
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement descriptor.sourceClauseMember
  have routeHead :
      route.head? = some descriptor.metadata.sourceClause.position := by
    simpa [route, PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicVariablePlacement.translation, Cell.scale, Cell.sub,
      sourceAnchor] using routeEndpoints.1
  have routeZeroEq :
      route.getD 0 (0, 0) = descriptor.metadata.sourceClause.position := by
    cases routeEq : route with
    | nil =>
        rw [routeEq] at routeLength
        simp at routeLength
    | cons first rest =>
        rw [routeEq] at routeHead
        simpa using Option.some.inj routeHead
  have sourceMargin := refinedSource_clause_position_margin
    presentation descriptor.sourceClauseMember
  have reservedBounds := routePoints_one_two_inSquare
    presentation descriptor.sourceClauseMember descriptor.sourceLiteralMember
  have zeroBounds :
      0 < (route.getD 0 (0, 0)).1 ∧
        (route.getD 0 (0, 0)).1 <
          (refinedPlacement sourcePlacement).period ∧
        0 < (route.getD 0 (0, 0)).2 ∧
        (route.getD 0 (0, 0)).2 <
          (refinedPlacement sourcePlacement).period := by
    rw [routeZeroEq]
    omega
  have oneTwoBounds :
      (0 < (route.getD 1 (0, 0)).1 ∧
        (route.getD 1 (0, 0)).1 <
          (refinedPlacement sourcePlacement).period ∧
        0 < (route.getD 1 (0, 0)).2 ∧
        (route.getD 1 (0, 0)).2 <
          (refinedPlacement sourcePlacement).period) ∧
      (0 < (route.getD 2 (0, 0)).1 ∧
        (route.getD 2 (0, 0)).1 <
          (refinedPlacement sourcePlacement).period ∧
        0 < (route.getD 2 (0, 0)).2 ∧
        (route.getD 2 (0, 0)).2 <
          (refinedPlacement sourcePlacement).period) := by
    simpa [route, routePoint] using reservedBounds
  apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
  apply finalPositionInFundamentalSquare_of_refinedBounds presentation
  rcases pointCases with pointEq | pointOne | pointTwo
  · simpa [pointEq] using zeroBounds
  · simpa [pointOne] using oneTwoBounds.1
  · simpa [pointTwo] using oneTwoBounds.2

/-- Descriptor shape determines the exact raw output literal, and hence
whether the final fresh-variable gauge is zero or cancels the source
occurrence offset. -/
theorem outputLiteral_classify
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    (descriptor.fragment = .whole ∧
        taggedIncidence.1.literal =
          liftLiteral descriptor.sourceLiteral) ∨
      (descriptor.fragment = .prefix ∧
        taggedIncidence.1.literal =
          complementLiteral descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex descriptor.sourceLiteral) ∨
      (descriptor.fragment = .middle ∧
        taggedIncidence.1.literal =
          complementFalseLiteral descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex descriptor.sourceLiteral) ∨
      (descriptor.fragment = .suffix ∧
        taggedIncidence.1.literal =
          originalFalseLiteral descriptor.sourceLiteral) := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, incidenceEq⟩
  have outputClauseEq : outputClause = descriptor.metadata.clause :=
    descriptor.outputClause_eq_metadataClause outputClauseMember
  subst outputClause
  have taggedLiteralEq : taggedIncidence.1.literal = outputLiteral :=
    congrArg CNFIncidence.literal incidenceEq
  have metadataMember :
      descriptor.metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    have rawMember : descriptor.metadata ∈
        clauseMetadata source sourcePlacement presentation.routes := by
      rcases List.getElem?_eq_some_iff.mp descriptor.metadataLookup with
        ⟨metadataIndexLt, metadataAt⟩
      rw [← metadataAt]
      exact List.getElem_mem metadataIndexLt
    simpa only [clauseMetadata] using rawMember
  rcases descriptor.shape.classifyWithShift with
      wholeCase | prefixCase | middleCase | suffixCase
  · rcases wholeCase with
      ⟨fragmentEq, _shiftEq, originEq, sourceIndex, compatible⟩
    refine Or.inl ⟨fragmentEq, taggedLiteralEq.trans ?_⟩
    have normalizedClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) metadataMember originEq
    have normalizedLiteralMember :
        (outputLiteral, descriptor.sourceLiteralIndex) ∈
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            descriptor.metadata.sourceClauseIndex
            descriptor.metadata.sourceClause).literals.zipIdx := by
      rw [sourceIndex, ← normalizedClauseEq]
      exact outputLiteralMember
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp descriptor.sourceLiteralMember
    rw [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?,
      sourceLiteralLookup] at outputLiteralLookup
    have normalizedEq :
        normalizeLiteral descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex descriptor.sourceLiteral =
          outputLiteral := by
      simpa using Option.some.inj outputLiteralLookup
    simpa [normalizeLiteral, compatible] using normalizedEq.symm
  · rcases prefixCase with
      ⟨fragmentEq, _shiftEq, originEq, sourceIndex, incompatible⟩
    refine Or.inr (Or.inl ⟨fragmentEq, taggedLiteralEq.trans ?_⟩)
    have normalizedClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) metadataMember originEq
    have normalizedLiteralMember :
        (outputLiteral, descriptor.sourceLiteralIndex) ∈
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            descriptor.metadata.sourceClauseIndex
            descriptor.metadata.sourceClause).literals.zipIdx := by
      rw [sourceIndex, ← normalizedClauseEq]
      exact outputLiteralMember
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp descriptor.sourceLiteralMember
    rw [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?,
      sourceLiteralLookup] at outputLiteralLookup
    have normalizedEq :
        normalizeLiteral descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex descriptor.sourceLiteral =
          outputLiteral := by
      simpa using Option.some.inj outputLiteralLookup
    simpa [normalizeLiteral, incompatible] using normalizedEq.symm
  · rcases middleCase with
      ⟨fragmentEq, _shiftEq, originEq, outputIndex, _incompatible⟩
    refine Or.inr (Or.inr (Or.inl
      ⟨fragmentEq, taggedLiteralEq.trans ?_⟩))
    have complementClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) metadataMember originEq
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp outputLiteralMember
    rw [outputIndex, complementClauseEq] at outputLiteralLookup
    have outputLiteralEq :
        complementFalseLiteral descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex descriptor.sourceLiteral =
          outputLiteral := by
      simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
        complementClause] using outputLiteralLookup
    exact outputLiteralEq.symm
  · rcases suffixCase with
      ⟨fragmentEq, _shiftEq, originEq, outputIndex, _incompatible⟩
    refine Or.inr (Or.inr (Or.inr
      ⟨fragmentEq, taggedLiteralEq.trans ?_⟩))
    have complementClauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) metadataMember originEq
    have outputLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp outputLiteralMember
    rw [outputIndex, complementClauseEq] at outputLiteralLookup
    have outputLiteralEq :
        originalFalseLiteral descriptor.sourceLiteral = outputLiteral := by
      simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
        complementClause] using outputLiteralLookup
    exact outputLiteralEq.symm

end RawRouteDescriptor

/-- Every raw split incidence route stays in the same ordinary open halo as
the complete refined source route from which it was cut. -/
theorem rawIncidenceRoutes_rebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ∀ taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx,
      ∀ point ∈ PeriodicOrthocrossing.translatePolyline
        ((rawPlacement sourcePlacement presentation.routes).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor taggedIncidence.1.clause)
            taggedIncidence.1.literal.offset))
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          taggedIncidence.1.clauseIndex
          taggedIncidence.1.literalIndex).reverse,
        (rawIncidenceDrawing
          presentation.toContinuousPlanarIncidencePresentation)
          |>.PositionInExpandedSquare point := by
  intro taggedIncidence taggedIncidenceMember point pointMember
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  let descriptor :=
    (exists_rawRouteDescriptor continuous taggedIncidenceMember).some
  have refinedMember :
      point ∈
        ((refinedContinuousPlanarPresentation continuous)
          |>.toPlanarIncidencePresentation
          |>.variableToClauseRoute descriptor.sourceIncidence) :=
    descriptor.rebasedPoint_mem_refinedVariableToClauseRoute
      taggedIncidenceMember pointMember
  have refinedInside :=
    (refinedRouteFamily_rebasedRoutePointsInExpandedSquare presentation)
      (descriptor.sourceIncidence, descriptor.sourceRouteIndex)
      descriptor.sourceTaggedIncidenceMember point refinedMember
  have refinedGridSize :
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (refinedContinuousPlanarPresentation
          presentation.toContinuousPlanarIncidencePresentation).routes).gridSize =
          (refinedPlacement sourcePlacement).period :=
    PositionedPeriodicCNF.incidenceDrawing_gridSize
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (refinedContinuousPlanarPresentation
        presentation.toContinuousPlanarIncidencePresentation).routes
      (refinedContinuousPlanarPresentation
        presentation.toContinuousPlanarIncidencePresentation).periodPositive
  have rawGridSize :
      (rawIncidenceDrawing
        presentation.toContinuousPlanarIncidencePresentation).gridSize =
          (rawPlacement sourcePlacement presentation.routes).period := by
    simpa [rawIncidenceDrawing] using
      PositionedPeriodicCNF.incidenceDrawing_gridSize
        (rawFormula source sourcePlacement presentation.routes)
        (rawPlacement sourcePlacement presentation.routes)
        (rawIncidenceRoutes source sourcePlacement presentation.routes)
        (rawPlacement_periodPositive continuous)
  unfold PeriodicGridDrawing.PositionInExpandedSquare at refinedInside ⊢
  rw [refinedGridSize] at refinedInside
  rw [rawGridSize]
  simpa only [rawPlacement_period] using refinedInside

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
