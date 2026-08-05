import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusNormalization

/-!
# Rebased-route radius bounds for the retained planar-SAT source

The finite retained component bound is transported through literal
periodicization, opaque wrapping, the canonical variable gauge, and clause
anchor normalization.  This produces the first complete variable-centered
one-period certificate in the retained reduction pipeline.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Before anchor normalization, every retained physical route point is
within one period of its gauged physical literal occurrence. -/
theorem
    retainedGaugedWrappedDrawingIncidenceRoutes_withinPhysicalLiteralPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.IncidenceRoutesWithinPhysicalLiteralPeriod
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula) := by
  intro positionedClause clauseIndex positionedClauseMember
    gaugedLiteral literalIndex gaugedLiteralMember point pointMember
  rw [gauged_clauses_eq_metadata formula, List.zipIdx_map]
    at positionedClauseMember
  rcases List.mem_map.mp positionedClauseMember with
    ⟨taggedMetadata, taggedMetadataMember,
      positionedClauseEqual⟩
  have clauseIndexEqual : taggedMetadata.2 = clauseIndex :=
    congrArg Prod.snd positionedClauseEqual
  have positionedClauseValueEqual :
      positionedClause =
        ⟨taggedMetadata.1.clause.position,
          (wrapPeriodicPlanarSATClause
            (periodicizePlanarSATClause formula
              taggedMetadata.1.clause)).variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula)⟩ :=
    (congrArg Prod.fst positionedClauseEqual).symm
  subst clauseIndex
  subst positionedClause
  change
    (gaugedLiteral, literalIndex) ∈
      (((taggedMetadata.1.clause.literals.map
          (periodicizePlanarSATLiteral formula)).map
            wrapPeriodicPlanarSATLiteral).map
              (PeriodicLiteral.variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula))).zipIdx
    at gaugedLiteralMember
  rw [← List.map_map, ← List.map_map,
    List.zipIdx_map] at gaugedLiteralMember
  rcases List.mem_map.mp gaugedLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember, gaugedLiteralEqual⟩
  have literalIndexEqual : taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd gaugedLiteralEqual
  have gaugedLiteralValueEqual :
      gaugedLiteral =
        (wrapPeriodicPlanarSATLiteral
          (periodicizePlanarSATLiteral formula taggedLiteral.1))
          |>.variableGauge
            (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
              formula) :=
    (congrArg Prod.fst gaugedLiteralEqual).symm
  subst literalIndex
  subst gaugedLiteral
  have metadataMember :
      taggedMetadata.1 ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.fst_mem_of_mem_zipIdx taggedMetadataMember
  have valid : taggedMetadata.1.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid formula metadataMember
  have finiteBound :=
    metadata_localRoutePoint_within_variablePeriod
      wellFormed degree isLocal taggedMetadata.1 valid
      taggedLiteralMember pointMember
  have finiteEndpoints :=
    (taggedMetadata.1.source.incidenceDrawing formula).physicalRoutesMatch
      (taggedMetadata.1.retainedLocalDrawingRoutesMatch
        wellFormed degree isLocal valid)
      taggedMetadata.1.clause taggedMetadata.1.source.localClauseIndex
      (taggedMetadata.1.retainedLocalClauseMember
        wellFormed degree isLocal valid)
      taggedLiteral.1 taggedLiteral.2 taggedLiteralMember
  rw [DrawingPlanarSATClauseSource.incidenceDrawing_variablePosition]
    at finiteEndpoints
  have gaugedEndpoints :=
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
      formula wellFormed degree isLocal
      ⟨taggedMetadata.1.clause.position,
        (wrapPeriodicPlanarSATClause
          (periodicizePlanarSATClause formula
            taggedMetadata.1.clause)).variableGauge
              (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                formula)⟩
      taggedMetadata.2
      (by simpa [gauged_clauses_eq_metadata formula] using
        taggedMetadataMember)
      ((wrapPeriodicPlanarSATLiteral
        (periodicizePlanarSATLiteral formula taggedLiteral.1))
        |>.variableGauge
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula))
      taggedLiteral.2
      (by
        change
          ((wrapPeriodicPlanarSATLiteral
              (periodicizePlanarSATLiteral formula taggedLiteral.1))
              |>.variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula),
            taggedLiteral.2) ∈
            (((taggedMetadata.1.clause.literals.map
                (periodicizePlanarSATLiteral formula)).map
                  wrapPeriodicPlanarSATLiteral).map
                    (PeriodicLiteral.variableGauge
                      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                        formula))).zipIdx
        rw [← List.map_map, ← List.map_map, List.zipIdx_map]
        exact List.mem_map.mpr
          ⟨taggedLiteral, taggedLiteralMember, rfl⟩)
  have centersEqual :
      drawingPlanarSATVariablePosition formula taggedLiteral.1.1 =
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          |>.literalPosition
            ((wrapPeriodicPlanarSATLiteral
              (periodicizePlanarSATLiteral formula taggedLiteral.1))
              |>.variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula)) := by
    apply Option.some.inj
    exact finiteEndpoints.2.symm.trans gaugedEndpoints.2
  rw [← centersEqual]
  simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement] using finiteBound

/-- Anchor normalization turns the retained physical endpoint certificate
into the variable-centered rebased-route certificate. -/
theorem
    retainedAnchorNormalizedGaugedWrappedDrawingIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula)) := by
  exact
    (retainedGaugedWrappedDrawingIncidenceRoutes_withinPhysicalLiteralPeriod
      formula wellFormed degree isLocal).anchorNormalize

/-- Literal-list deduplication reuses the zero-anchor representative route,
so it preserves the retained variable-centered certificate exactly. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula) := by
  let source :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceRoutes :=
    PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      placement
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
  have sourceBounds :
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
        source placement sourceRoutes := by
    simpa [source, placement, sourceRoutes] using
      retainedAnchorNormalizedGaugedWrappedDrawingIncidenceRoutes_withinVariablePeriod
        formula wellFormed degree isLocal
  intro retainedClause clauseIndex retainedClauseMember
    literal literalIndex literalMember point pointMember
  have retainedClauseLookup :
      source.deduplicateByLiterals.clauses[clauseIndex]? =
        some retainedClause := by
    apply (List.mem_zipIdx_iff_getElem?).mp
    simpa [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using retainedClauseMember
  have retainedClauseMem :
      retainedClause ∈ source.deduplicateByLiterals.clauses :=
    List.fst_mem_of_mem_zipIdx (by
      simpa [source,
        retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
        using retainedClauseMember)
  rcases exists_representativeClause_of_mem_deduplicateByLiterals
      source retainedClause retainedClauseMem with
    ⟨sourceClause, sourceClauseLookup, sourceClauseLiterals⟩
  have sourceClauseMember :
      (sourceClause,
        source.representativeClauseIndex retainedClause.literals) ∈
          source.clauses.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr sourceClauseLookup
  have sourceLiteralMember :
      (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
    simpa [sourceClauseLiterals] using literalMember
  have anchorZero :
      PeriodicCNF.clauseAnchor retainedClause.literals = (0, 0) := by
    apply clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      placement retainedClause
    simpa [source] using retainedClauseMem
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨storedPoint, storedPointMember, rfl⟩
  have storedPointMember' :
      storedPoint ∈
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex :=
    List.mem_reverse.mp storedPointMember
  have sourcePointMember :
      storedPoint ∈
        sourceRoutes
          (source.representativeClauseIndex retainedClause.literals)
          literalIndex := by
    apply mem_sourceRoute_of_mem_deduplicatedIncidenceRoute_of_anchor_zero
      source placement sourceRoutes retainedClauseLookup anchorZero
    simpa [source, placement, sourceRoutes,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes]
      using storedPointMember'
  apply sourceBounds sourceClause
    (source.representativeClauseIndex retainedClause.literals)
    sourceClauseMember literal literalIndex sourceLiteralMember
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.mem_map.mpr
  refine ⟨storedPoint, List.mem_reverse.mpr sourcePointMember, ?_⟩
  simp [sourceClauseLiterals]

end PeriodicOrthocrossing
end LeanTrominoes
