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

/-- Periodicization, opaque wrapping, and the canonical variable gauge leave
the displayed physical position of a retained literal unchanged. -/
private theorem retainedGaugedWrappedLiteralPosition_eq_finite
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PlanarSATVariable Variable × Bool) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).literalPosition
        (PeriodicLiteral.variableGauge
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
          (wrapPeriodicPlanarSATLiteral
            (periodicizePlanarSATLiteral formula literal))) =
      drawingPlanarSATVariablePosition formula literal.1 := by
  calc
    _ = (wrappedDrawingPeriodicPlanarSATPlacement formula).literalPosition
          (wrapPeriodicPlanarSATLiteral
            (periodicizePlanarSATLiteral formula literal)) :=
      PeriodicVariablePlacement.variableGauge_literalPosition
        (wrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
        (wrapPeriodicPlanarSATLiteral
          (periodicizePlanarSATLiteral formula literal))
    _ = (drawingPeriodicPlanarSATPlacement formula).literalPosition
          (periodicizePlanarSATLiteral formula literal) := rfl
    _ = drawingPlanarSATVariablePosition formula literal.1 :=
      periodicizePlanarSATLiteral_position formula literal

/-- Membership in the gauged positioned source can be decoded back to the
retained finite metadata and literal at the same indices. -/
private theorem exists_retainedMetadata_of_gauged_members
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {positionedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (positionedClauseMember :
      (positionedClause, clauseIndex) ∈
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {gaugedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (gaugedLiteralMember :
      (gaugedLiteral, literalIndex) ∈
        positionedClause.literals.zipIdx) :
    ∃ metadata literal,
      (metadata, clauseIndex) ∈
          (retainedDrawingPlanarSATClauseMetadata formula).zipIdx ∧
        (literal, literalIndex) ∈ metadata.clause.literals.zipIdx ∧
        gaugedLiteral =
          PeriodicLiteral.variableGauge
            (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
            (wrapPeriodicPlanarSATLiteral
              (periodicizePlanarSATLiteral formula literal)) := by
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
  rw [List.map_map, List.map_map,
    List.zipIdx_map] at gaugedLiteralMember
  rcases List.mem_map.mp gaugedLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember, gaugedLiteralEqual⟩
  have literalIndexEqual : taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd gaugedLiteralEqual
  have gaugedLiteralValueEqual :
      gaugedLiteral =
        PeriodicLiteral.variableGauge
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
          (wrapPeriodicPlanarSATLiteral
            (periodicizePlanarSATLiteral formula taggedLiteral.1)) :=
    (congrArg Prod.fst gaugedLiteralEqual).symm
  subst literalIndex
  exact ⟨taggedMetadata.1, taggedLiteral.1,
    taggedMetadataMember, taggedLiteralMember,
    gaugedLiteralValueEqual⟩

/-- The finite local route bound, expressed at one decoded gauged literal. -/
private theorem retainedMetadataRoutePoint_within_gaugedLiteralPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    {clauseIndex : Nat}
    (metadataMember :
      (metadata, clauseIndex) ∈
        (retainedDrawingPlanarSATClauseMetadata formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDrawingPlanarSATLocalIncidenceRoutes
          formula clauseIndex literalIndex) :
    WithinCoordinateRadius
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).period
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        |>.literalPosition
          (PeriodicLiteral.variableGauge
            (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
            (wrapPeriodicPlanarSATLiteral
              (periodicizePlanarSATLiteral formula literal))))
      point := by
  have metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata formula)[clauseIndex]? =
        some metadata :=
    (List.mem_zipIdx_iff_getElem?).mp metadataMember
  simp only [retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] at pointMember
  have metadataMem :
      metadata ∈ retainedDrawingPlanarSATClauseMetadata formula :=
    List.fst_mem_of_mem_zipIdx metadataMember
  have valid : metadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid formula metadataMem
  have finiteBound :=
    metadata_localRoutePoint_within_variablePeriod
      wellFormed degree isLocal metadata valid
      literalMember pointMember
  rw [retainedGaugedWrappedLiteralPosition_eq_finite]
  change WithinCoordinateRadius
    (drawingPeriodicPlanarSATPlacement formula).period
    (drawingPlanarSATVariablePosition formula literal.1) point
  exact finiteBound

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
  rcases exists_retainedMetadata_of_gauged_members
      formula positionedClauseMember gaugedLiteralMember with
    ⟨metadata, literal, metadataMember,
      literalMember, gaugedLiteralEq⟩
  subst gaugedLiteral
  exact retainedMetadataRoutePoint_within_gaugedLiteralPeriod
    formula wellFormed degree isLocal metadataMember
    literalMember pointMember

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
  have anchorZero :
      ∀ clause ∈ source.deduplicateByLiterals.clauses,
        PeriodicCNF.clauseAnchor clause.literals = (0, 0) := by
    intro clause clauseMember
    apply clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      placement clause
    simpa [source, placement,
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using clauseMember
  have deduplicatedBounds :=
    sourceBounds.deduplicateByLiterals anchorZero
  simpa [source, placement, sourceRoutes,
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes]
    using deduplicatedBounds

end PeriodicOrthocrossing
end LeanTrominoes
