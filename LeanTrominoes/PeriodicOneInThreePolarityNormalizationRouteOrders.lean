import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPresentationProperties
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport

/-!
# Clause-route order under polarity normalization

Ternary output clauses are normalized copies of source clauses.  Their three
routes retain the source routes' clause-side first directions, while every
new complement clause is binary.  Thus the clockwise ternary clause order
needed by the 3DM endpoint fans survives route splitting and the final gauge.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Keeping the first two points of a nondegenerate route does not change its
first directed axis. -/
theorem polylineFirstDirection_take_two
    (points : List Cell) (length : 2 ≤ points.length) :
    AxisDirection.polylineFirstDirection (points.take 2) =
      AxisDirection.polylineFirstDirection points := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest => rfl

/-- Ordered unit subdivision of the scaled source routes preserves ternary
clause order. -/
theorem refinedRoutes_ternaryClauseRoutesInClockwiseOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (ordered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (refinedSource source sourcePlacement).TernaryClauseRoutesInClockwiseOrder
      (refinedRoute presentation.routes) := by
  have scaledOrdered :
      (refinedSource source sourcePlacement).TernaryClauseRoutesInClockwiseOrder
        (scaledSourcePresentation presentation).routes := by
    exact
      (ordered.anchorNormalize sourcePlacement).scaleCoordinates
        refinementFactor refinementFactor_positive
  intro clause clauseIndex clauseMember clauseArity
  have clockwise :=
    scaledOrdered clause clauseIndex clauseMember clauseArity
  have directionEq :
      ∀ literalIndex, literalIndex < 3 →
        AxisDirection.polylineFirstDirection
            (refinedRoute presentation.routes clauseIndex literalIndex) =
          AxisDirection.polylineFirstDirection
            ((scaledSourcePresentation presentation).routes
              clauseIndex literalIndex) := by
    intro literalIndex literalIndexLt
    have literalIndexLtLength : literalIndex < clause.literals.length := by
      omega
    let literal := clause.literals[literalIndex]
    have literalLookup :
        clause.literals[literalIndex]? = some literal := by
      exact List.getElem?_eq_getElem literalIndexLtLength
    have literalMember :
        (literal, literalIndex) ∈ clause.literals.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr literalLookup
    apply AxisDirection.polylineFirstDirection_unitSubdividePolyline
    · simpa [scaledSourcePresentation_routes,
        scalePolyline] using
        sourceRoute_length_ge_two_of_refined_members presentation
          clauseMember literalMember
    · exact
        PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
          (sourceRoute_orthogonal_of_refined_members presentation
            clauseMember literalMember)
          refinementFactor_positive
  rw [directionEq 0 (by decide), directionEq 1 (by decide),
    directionEq 2 (by decide)]
  exact clockwise

/-- A normalized main incidence keeps the first directed axis of its
complete refined source route, whether or not that route is split. -/
theorem rawRouteForMetadata_normalized_firstDirection
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (originEq : metadata.origin = .normalized)
    (literalLookup :
      metadata.sourceClause.literals[literalIndex]? = some sourceLiteral)
    (length :
      2 ≤ (refinedRoute sourceRoutes metadata.sourceClauseIndex
        literalIndex).length) :
    AxisDirection.polylineFirstDirection
        (rawRouteForMetadata sourcePlacement sourceRoutes metadata
          literalIndex) =
      AxisDirection.polylineFirstDirection
        (refinedRoute sourceRoutes metadata.sourceClauseIndex literalIndex) := by
  by_cases compatible :
      sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex
  · rw [rawRouteForMetadata_normalized_compatible
      sourcePlacement sourceRoutes metadata sourceLiteral literalIndex
      originEq literalLookup compatible]
  · rw [rawRouteForMetadata_normalized_incompatible
      sourcePlacement sourceRoutes metadata sourceLiteral literalIndex
      originEq literalLookup compatible]
    exact polylineFirstDirection_take_two _ length

/-- Before the final gauge, every ternary output clause retains clockwise
route order from its source clause. -/
theorem rawIncidenceRoutes_ternaryClauseRoutesInClockwiseOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (ordered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (rawFormula source sourcePlacement presentation.routes)
      |>.TernaryClauseRoutesInClockwiseOrder
        (rawIncidenceRoutes source sourcePlacement presentation.routes) := by
  intro outputClause clauseIndex clauseMember outputArity
  rcases
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_lookup
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement)
        clauseMember with
    ⟨metadata, metadataLookup, metadataClauseEq⟩
  have metadataMember :
      metadata ∈ clauseMetadata source sourcePlacement presentation.routes :=
    by
      rcases List.getElem?_eq_some_iff.mp metadataLookup with
        ⟨indexLt, metadataAt⟩
      rw [← metadataAt]
      exact List.getElem_mem _
  have sourceClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement presentation.routes)
      (refinedSource source sourcePlacement) metadataMember
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
      have sourceArity : metadata.sourceClause.literals.length = 3 := by
        rw [← metadataClauseEq] at outputArity
        rw [normalizedClauseEq] at outputArity
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
          PeriodicOneInThreePolarityNormalization.normalizeClause_length]
          using outputArity
      have refinedOrdered :=
        refinedRoutes_ternaryClauseRoutesInClockwiseOrder
          presentation ordered metadata.sourceClause
          metadata.sourceClauseIndex sourceClauseMember sourceArity
      have directionEq :
          ∀ literalIndex, literalIndex < 3 →
            AxisDirection.polylineFirstDirection
                (rawIncidenceRoutes source sourcePlacement presentation.routes
                  clauseIndex literalIndex) =
              AxisDirection.polylineFirstDirection
                (refinedRoute presentation.routes
                  metadata.sourceClauseIndex literalIndex) := by
        intro literalIndex literalIndexLt
        have literalIndexLtLength :
            literalIndex < metadata.sourceClause.literals.length := by
          omega
        let sourceLiteral :=
          metadata.sourceClause.literals[literalIndex]
        have sourceLiteralLookup :
            metadata.sourceClause.literals[literalIndex]? =
              some sourceLiteral := by
          exact List.getElem?_eq_getElem literalIndexLtLength
        rw [rawIncidenceRoutes_of_metadata_lookup
          source sourcePlacement presentation.routes metadata
          clauseIndex literalIndex metadataLookup]
        apply rawRouteForMetadata_normalized_firstDirection
          sourcePlacement presentation.routes metadata sourceLiteral
            literalIndex originEq sourceLiteralLookup
        have sourceLiteralMember :
            (sourceLiteral, literalIndex) ∈
              metadata.sourceClause.literals.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr sourceLiteralLookup
        exact (refinedRoute_length_ge_four_of_members presentation
          sourceClauseMember sourceLiteralMember).trans' (by decide)
      rw [directionEq 0 (by decide), directionEq 1 (by decide),
        directionEq 2 (by decide)]
      exact refinedOrdered
  | complement sourceLiteralIndex sourceLiteral =>
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)
          metadataMember originEq
      rw [← metadataClauseEq, complementClauseEq] at outputArity
      simp [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
        PeriodicOneInThreePolarityNormalization.complementClause] at outputArity

/-- The final variable gauge preserves the routed normalized formula's
clockwise ternary-clause order. -/
theorem incidenceRoutes_ternaryClauseRoutesInClockwiseOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (ordered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (formula source sourcePlacement presentation.routes)
      |>.TernaryClauseRoutesInClockwiseOrder
        (incidenceRoutes source sourcePlacement presentation.routes) := by
  exact
    (rawIncidenceRoutes_ternaryClauseRoutesInClockwiseOrder
      presentation ordered).variableGaugeCanonicalIncidenceRoutes freshGauge

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
