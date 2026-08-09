import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertices

/-!
# Fundamental-square bounds for polarity-normalization vertices

Threefold scaling puts every retained source vertex at least three lattice
units from the boundary of the refined fundamental square.  The two reserved
unit-subdivision points therefore remain strictly inside that square in every
cardinal direction.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- A retained refined clause position is three times the canonical position
of the source clause with the same presentation index. -/
theorem exists_sourceClause_of_refinedSource_clause_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {refinedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (refinedClauseMember :
      (refinedClause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    ∃ sourceClause,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      refinedClause.position =
        Cell.scale refinementFactor
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause) := by
  unfold refinedSource at refinedClauseMember
  rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
      at refinedClauseMember
  rcases List.mem_map.mp refinedClauseMember with
    ⟨normalizedTagged, normalizedTaggedMember, refinedTaggedEq⟩
  rcases normalizedTagged with ⟨normalizedClause, normalizedIndex⟩
  have refinedClauseEq :
      normalizedClause.scale refinementFactor = refinedClause := by
    simpa only [Prod.map, id_eq] using congrArg Prod.fst refinedTaggedEq
  have normalizedIndexEq : normalizedIndex = clauseIndex := by
    simpa only [Prod.map, id_eq] using congrArg Prod.snd refinedTaggedEq
  rw [PositionedPeriodicCNF.anchorNormalize, List.zipIdx_map]
      at normalizedTaggedMember
  rcases List.mem_map.mp normalizedTaggedMember with
    ⟨sourceTagged, sourceTaggedMember, normalizedTaggedEq⟩
  rcases sourceTagged with ⟨sourceClause, sourceIndex⟩
  have sourceIndexEq : sourceIndex = normalizedIndex := by
    simpa only [Prod.map, id_eq] using congrArg Prod.snd normalizedTaggedEq
  subst normalizedIndex
  subst sourceIndex
  refine ⟨sourceClause, sourceTaggedMember, ?_⟩
  have normalizedClauseEq :
      ({ position :=
          PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause
         literals := sourceClause.literals.anchorNormalize } :
        PositionedPeriodicClause Variable) = normalizedClause := by
    simpa only [Prod.map, id_eq] using
      congrArg Prod.fst normalizedTaggedEq
  calc
    refinedClause.position =
        (normalizedClause.scale refinementFactor).position :=
      congrArg PositionedPeriodicClause.position refinedClauseEq.symm
    _ = Cell.scale refinementFactor normalizedClause.position := rfl
    _ = Cell.scale refinementFactor
        (PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause) := by
      rw [← normalizedClauseEq]

/-- A retained refined clause has a two-unit margin on all four sides of the
refined fundamental square. -/
theorem refinedSource_clause_position_margin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {refinedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (refinedClauseMember :
      (refinedClause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    2 < refinedClause.position.1 ∧
      refinedClause.position.1 + 2 <
        (refinedPlacement sourcePlacement).period ∧
      2 < refinedClause.position.2 ∧
      refinedClause.position.2 + 2 <
        (refinedPlacement sourcePlacement).period := by
  rcases exists_sourceClause_of_refinedSource_clause_mem
      source sourcePlacement refinedClauseMember with
    ⟨sourceClause, sourceClauseMember, refinedPositionEq⟩
  have canonicalPositionMember :
      PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause ∈
        PositionedPeriodicCNF.incidenceVertexPositions
          source sourcePlacement := by
    unfold PositionedPeriodicCNF.incidenceVertexPositions
    apply List.mem_append_right
    exact List.mem_map.mpr
      ⟨sourceClause, List.fst_mem_of_mem_zipIdx sourceClauseMember, rfl⟩
  have sourceBounds :=
    presentation.compatible.2.2.2.2.1 _ canonicalPositionMember
  unfold PeriodicGridDrawing.PositionInFundamentalSquare at sourceBounds
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    source sourcePlacement presentation.routes presentation.periodPositive]
      at sourceBounds
  rcases PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement sourceClause with ⟨sourceX, sourceY⟩
  have refinedXEq := congrArg Prod.fst refinedPositionEq
  have refinedYEq := congrArg Prod.snd refinedPositionEq
  simp [refinementFactor, refinedPlacement,
    PeriodicVariablePlacement.scale, Cell.scale] at refinedXEq refinedYEq ⊢
  omega

/-- Two consecutive unit steps from a point with a two-unit boundary margin
remain strictly inside the same square. -/
theorem first_two_unit_points_inSquare
    (route : List Cell)
    (period : Nat)
    (length : 4 ≤ route.length)
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep)
    (start : Cell)
    (headEq : route.head? = some start)
    (margin :
      2 < start.1 ∧ start.1 + 2 < period ∧
        2 < start.2 ∧ start.2 + 2 < period) :
    (0 < (route.getD 1 (0, 0)).1 ∧
        (route.getD 1 (0, 0)).1 < period ∧
        0 < (route.getD 1 (0, 0)).2 ∧
        (route.getD 1 (0, 0)).2 < period) ∧
      (0 < (route.getD 2 (0, 0)).1 ∧
        (route.getD 2 (0, 0)).1 < period ∧
        0 < (route.getD 2 (0, 0)).2 ∧
        (route.getD 2 (0, 0)).2 < period) := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              have firstSecond :
                  AxisDirection.IsUnitAxisStep first second :=
                (List.isChain_cons_cons.mp unitSteps).1
              have secondThird :
                  AxisDirection.IsUnitAxisStep second third :=
                (List.isChain_cons_cons.mp
                  (List.isChain_cons_cons.mp unitSteps).2).1
              have firstEq : first = start := by
                simpa using Option.some.inj headEq
              subst first
              rcases start with ⟨startX, startY⟩
              rcases firstSecond with
                ⟨firstDirection, firstGenuine, secondEq⟩
              rcases secondThird with
                ⟨secondDirection, secondGenuine, thirdEq⟩
              cases firstDirection <;> cases secondDirection <;>
                simp_all [AxisDirection.IsGenuine,
                  AxisDirection.step, Cell.add] <;> omega

/-- The fresh-variable and complement-clause subdivision points of every
genuine refined source incidence lie strictly inside the refined fundamental
square. -/
theorem routePoints_one_two_inSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx) :
    let fresh : FreshOccurrence Variable :=
      ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral)
    (0 < (routePoint presentation.routes fresh 1).1 ∧
        (routePoint presentation.routes fresh 1).1 <
          (refinedPlacement sourcePlacement).period ∧
        0 < (routePoint presentation.routes fresh 1).2 ∧
        (routePoint presentation.routes fresh 1).2 <
          (refinedPlacement sourcePlacement).period) ∧
      (0 < (routePoint presentation.routes fresh 2).1 ∧
        (routePoint presentation.routes fresh 2).1 <
          (refinedPlacement sourcePlacement).period ∧
        0 < (routePoint presentation.routes fresh 2).2 ∧
        (routePoint presentation.routes fresh 2).2 <
          (refinedPlacement sourcePlacement).period) := by
  dsimp only
  have routeLength := refinedRoute_length_ge_four_of_members
    presentation sourceClauseMember sourceLiteralMember
  have routeUnitSteps := refinedRoute_unitSteps_of_members
    presentation sourceClauseMember sourceLiteralMember
  have routeEndpoints :=
    (refinedRouteFamily presentation).endpoints
      sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at routeEndpoints
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement sourceClauseMember
  have routeHead :
      (refinedRoute presentation.routes
        sourceClauseIndex sourceLiteralIndex).head? =
        some sourceClause.position := by
    simpa [PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicVariablePlacement.translation, Cell.scale, Cell.sub,
      sourceAnchor] using routeEndpoints.1
  exact first_two_unit_points_inSquare
    (refinedRoute presentation.routes
      sourceClauseIndex sourceLiteralIndex)
    (refinedPlacement sourcePlacement).period
    routeLength routeUnitSteps sourceClause.position routeHead
    (refinedSource_clause_position_margin
      presentation sourceClauseMember)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
