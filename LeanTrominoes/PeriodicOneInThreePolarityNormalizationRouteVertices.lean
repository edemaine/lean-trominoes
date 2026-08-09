import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRoutePlanarity

/-!
# Vertex coordinates for polarity-normalized route subdivision

This file identifies the two new vertices inserted on an incompatible source
incidence after the fresh-variable gauge.  The fresh variable is exactly
subdivision point one, the complement clause is exactly subdivision point
two, and both generated clause kinds have zero canonical anchor.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Apply a variable gauge to one positioned clause while retaining its
displayed position. -/
def variableGaugeClause {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause Variable :=
  ⟨clause.position, clause.literals.variableGauge gauge⟩

/-- Gauging a positioned binary complement clause makes its fresh first
literal have offset zero, hence makes the common clause anchor zero. -/
@[simp]
theorem clauseAnchor_positionedComplementClause_variableGauge
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable) :
    PeriodicCNF.clauseAnchor
        (variableGaugeClause freshGauge
          (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
            (rawPositions sourcePlacement sourceRoutes)
            sourceClauseIndex sourceLiteralIndex sourceLiteral)).literals =
      (0, 0) := by
  rcases sourceLiteral with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
  simp [variableGaugeClause,
    PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
    PeriodicOneInThreePolarityNormalization.complementClause,
    PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
    PeriodicClause.variableGauge, PeriodicLiteral.variableGauge,
    PeriodicCNF.clauseAnchor, freshGauge, Cell.add, Cell.sub]

/-- The displayed position of a gauged complement clause is subdivision
point two. -/
@[simp]
theorem positionedComplementClause_variableGauge_position
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable) :
    (variableGaugeClause freshGauge
      (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
        (rawPositions sourcePlacement sourceRoutes)
        sourceClauseIndex sourceLiteralIndex sourceLiteral)).position =
      routePoint sourceRoutes
        ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 2 := by
  rfl

/-- Because its gauged anchor is zero, the canonical complement-clause
vertex is exactly subdivision point two. -/
@[simp]
theorem canonicalClausePosition_complement
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement sourceRoutes)
        (variableGaugeClause freshGauge
          (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
            (rawPositions sourcePlacement sourceRoutes)
            sourceClauseIndex sourceLiteralIndex sourceLiteral)) =
      routePoint sourceRoutes
        ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 2 := by
  simp [PositionedPeriodicCNF.canonicalClausePosition,
    PeriodicVariablePlacement.translation, Cell.scale, Cell.sub]

/-- A normalized main clause whose source anchor is zero retains anchor zero
through the fresh-variable gauge. -/
theorem clauseAnchor_normalizedClause_variableGauge_of_zero
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceAnchor :
      PeriodicCNF.clauseAnchor sourceClause.literals = (0, 0)) :
    PeriodicCNF.clauseAnchor
        (variableGaugeClause freshGauge
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            sourceClauseIndex sourceClause)).literals =
      (0, 0) := by
  cases sourceClause with
  | mk position literals =>
      cases literals with
      | nil => rfl
      | cons literal rest =>
          rcases literal with ⟨atom, offset, value⟩
          have offsetEq : offset = (0, 0) := by
            simpa [PeriodicCNF.clauseAnchor] using sourceAnchor
          subst offset
          by_cases compatible :
              value =
                PeriodicOneInThreePolarityNormalization.normalizedPolarity 0
          · simp [variableGaugeClause,
              PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
              PeriodicOneInThreePolarityNormalization.normalizeClause,
              PeriodicOneInThreePolarityNormalization.normalizeClauseFrom_cons,
              PeriodicOneInThreePolarityNormalization.normalizeLiteral,
              compatible,
              PeriodicOneInThreePolarityNormalization.liftLiteral,
              PeriodicClause.variableGauge, PeriodicLiteral.variableGauge,
              PeriodicCNF.clauseAnchor, freshGauge, Cell.add]
          · simp [variableGaugeClause,
              PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
              PeriodicOneInThreePolarityNormalization.normalizeClause,
              PeriodicOneInThreePolarityNormalization.normalizeClauseFrom_cons,
              PeriodicOneInThreePolarityNormalization.normalizeLiteral,
              compatible,
              PeriodicOneInThreePolarityNormalization.complementLiteral,
              PeriodicClause.variableGauge, PeriodicLiteral.variableGauge,
              PeriodicCNF.clauseAnchor, freshGauge, Cell.add, Cell.sub]

/-- Every final normalized main clause coming from the refined source has
zero canonical anchor. -/
theorem clauseAnchor_normalizedClause_variableGauge
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    PeriodicCNF.clauseAnchor
        (variableGaugeClause freshGauge
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            sourceClauseIndex sourceClause)).literals =
      (0, 0) :=
  clauseAnchor_normalizedClause_variableGauge_of_zero
    sourceClauseIndex sourceClause
    (refinedSource_clauseAnchor_eq_zero
      source sourcePlacement sourceClauseMember)

/-- The canonical vertex of a final normalized main clause is its retained
refined source position. -/
@[simp]
theorem canonicalClausePosition_normalized
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement sourceRoutes)
        (variableGaugeClause freshGauge
          (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
            sourceClauseIndex sourceClause)) =
      sourceClause.position := by
  rw [PositionedPeriodicCNF.canonicalClausePosition]
  rw [clauseAnchor_normalizedClause_variableGauge
    source sourcePlacement sourceClauseMember]
  simp [variableGaugeClause,
    PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
    PeriodicVariablePlacement.translation, Cell.scale, Cell.sub]

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
