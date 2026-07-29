import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRetainedRays
import LeanTrominoes.PositionedPeriodicCNFRetainedRayRasterization

/-!
# Orthogonally rasterized retained planar-SAT drawing

The final gauged and orbit-deduplicated planar-SAT drawing has exact
incidence endpoints and only the eleven retained ray slopes.  This file
combines those facts into a canonical retained-ray route package, then
defines its positive integral refinement and executable staircase
rasterization.

At this stage the refined drawing is certified to have the same logical
incidence graph, exact scaled endpoints, and wholly orthogonal routes.
Preservation of global planar separation is deliberately left as the next
geometric layer.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every genuine final route has its exact canonical clause and literal
endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
            clause) ∧
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
            clause literal) := by
  exact
    PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalEndpoints_of_routesMatch
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (drawingPeriodicPlanarSATPlacement_period_pos formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
        formula wellFormed degree isLocal)
      clauseMember literalMember

/-- The final route family packaged with both canonical endpoints and its
retained-ray certificate. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATCanonicalRetainedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula) where
  routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
        formula wellFormed degree isLocal
        clauseMember literalMember
  retained := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        formula wellFormed degree isLocal clausesNonempty
        (clause, clauseIndex) clauseMember
        (literal, literalIndex) literalMember

/-- Scale and rasterize every final retained planar-SAT incidence route. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  rasterizeRetainedIncidenceRoutes factor
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)

/-- The complete scaled and orthogonally rasterized periodic incidence
drawing. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (formula : PeriodicCNF Variable) :
    PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale factor)
    ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale factor)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
      factor formula)

/-- Every genuine rasterized route has its exact scaled canonical clause and
literal endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {scaledClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (scaledClauseMember :
      (scaledClause, clauseIndex) ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale factor).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        scaledClause.literals.zipIdx) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
        factor formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).scale factor)
            scaledClause) ∧
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
        factor formula clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).scale factor)
            scaledClause literal) := by
  rw [PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at scaledClauseMember
  rcases List.mem_map.mp scaledClauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      taggedClause.1.scale factor = scaledClause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst scaledClause
  have sourceLiteralMember :
      (literal, literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa using literalMember
  have sourceEndpoints :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula wellFormed degree isLocal
      taggedClauseMember sourceLiteralMember
  constructor
  · simpa
      [retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes]
      using
        rasterizeRetainedIncidenceRoutes_head?
          factor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          taggedClause.2 literalIndex sourceEndpoints.1
  · simpa
      [retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes]
      using
        rasterizeRetainedIncidenceRoutes_getLast?
          factor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          taggedClause.2 literalIndex sourceEndpoints.2

/-- Every genuine rasterized route is pointwise orthogonal. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {scaledClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (scaledClauseMember :
      (scaledClause, clauseIndex) ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale factor).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        scaledClause.literals.zipIdx) :
    OrthogonalPolyline
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
        factor formula clauseIndex literalIndex) := by
  rw [PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at scaledClauseMember
  rcases List.mem_map.mp scaledClauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      taggedClause.1.scale factor = scaledClause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst scaledClause
  have sourceLiteralMember :
      (literal, literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa using literalMember
  exact
    rasterizeRetainedIncidenceRoutes_orthogonal
      factorPositive
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      taggedClause.2 literalIndex
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        formula wellFormed degree isLocal clausesNonempty
        taggedClause taggedClauseMember
        (literal, literalIndex) sourceLiteralMember)

/-- The rasterized final routes, together with their exact scaled endpoint
and orthogonality certificates. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale factor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale factor) where
  routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes
      factor formula
  endpoints := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes_endpoints
        factor formula wellFormed degree isLocal
        scaledClauseMember literalMember
  orthogonal := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedIncidenceRoutes_orthogonal
        factorPositive formula wellFormed degree isLocal clausesNonempty
        scaledClauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
