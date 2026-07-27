import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

/-!
# The finite routed planar-SAT incidence drawing

The clause-source selector supplies one route for every literal occurrence
of the complete finite routed planar-SAT formula.  This file packages those
routes as a single `EmbeddedCNFIncidenceDrawing` and transfers the local
planarity certificates to every selected global route.

What remains for complete global planarity is isolated explicitly:
separation between routes selected from different local components, avoidance
of all global vertices, and distinctness of the assembled vertex positions.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The complete finite routed planar-SAT formula equipped with the
metadata-selected local route family. -/
irreducible_def drawingPlanarSATLocalIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) where
  formula := drawingPlanarSATFormula formula
  variablePosition := drawingPlanarSATVariablePosition formula
  routes := drawingPlanarSATLocalIncidenceRoutes formula

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).formula =
      drawingPlanarSATFormula formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_variablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).variablePosition =
      drawingPlanarSATVariablePosition formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_routes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).routes =
      drawingPlanarSATLocalIncidenceRoutes formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

/-- The assembled finite drawing has exact clause and variable endpoints. -/
theorem drawingPlanarSATLocalIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  rw [drawingPlanarSATLocalIncidenceDrawing_formula,
    drawingPlanarSATLocalIncidenceDrawing_variablePosition,
    drawingPlanarSATLocalIncidenceDrawing_routes]
  exact drawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
    formula wellFormed degree isLocal

/-- A valid metadata entry transfers its selected local drawing's route
simplicity to any genuine literal of the advertised clause. -/
theorem DrawingPlanarSATClauseMetadata.localRouteIsSimple
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      ((metadata.source.incidenceDrawing formula).routes
        metadata.source.localClauseIndex literalIndex) := by
  apply
    (metadata.source.incidenceDrawing formula)
      |>.embeddedRoute_isSimple_of_members
        (metadata.localDrawingIsPlanar
          wellFormed degree isLocal valid)
        (metadata.localClauseMember
          wellFormed degree isLocal valid)
        literalMember

/-- Two distinct local incidences selected from the same component inherit
that component's continuous route separation. -/
theorem DrawingPlanarSATClauseMetadata.localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.Valid formula)
    (secondValid : second.Valid formula)
    (sameSource : first.source = second.source)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (different :
      first.source.localClauseIndex ≠
          second.source.localClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((first.source.incidenceDrawing formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  have secondClauseMember :=
    second.localClauseMember
      wellFormed degree isLocal secondValid
  rw [← sameSource] at secondClauseMember different ⊢
  apply
    (first.source.incidenceDrawing formula)
      |>.embeddedRoutes_avoidEachOther_of_members
        (first.localDrawingIsPlanar
          wellFormed degree isLocal firstValid)
        (first.localClauseMember
          wellFormed degree isLocal firstValid)
        secondClauseMember
        firstLiteralMember secondLiteralMember different

/-- Every genuine global incidence exposes the exact valid local drawing,
local clause, local route, and local planarity certificate selected by its
source metadata. -/
theorem drawingPlanarSATLocalIncidence_localWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata,
      (drawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
          metadata.Valid formula ∧
            (metadata.clause,
                metadata.source.localClauseIndex) ∈
              (metadata.source.incidenceDrawing formula).formula.zipIdx ∧
              (literal, literalIndex) ∈
                metadata.clause.literals.zipIdx ∧
                drawingPlanarSATLocalIncidenceRoutes
                    formula clauseIndex literalIndex =
                  (metadata.source.incidenceDrawing formula).routes
                    metadata.source.localClauseIndex literalIndex ∧
                  (metadata.source.incidenceDrawing formula).IsPlanar := by
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  refine
    ⟨metadata, metadataLookup, clauseEqual, valid,
      metadata.localClauseMember
        wellFormed degree isLocal valid, ?_, ?_, ?_⟩
  · simpa [clauseEqual] using literalMember
  · simp [drawingPlanarSATLocalIncidenceRoutes, metadataLookup]
  · exact metadata.localDrawingIsPlanar
      wellFormed degree isLocal valid

/-- Every route in the assembled finite drawing is simple, because its
metadata-selected local component is continuously planar. -/
theorem drawingPlanarSATLocalIncidenceRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (drawingPlanarSATLocalIncidenceRoutes
        formula clauseIndex literalIndex) := by
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  have localLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have simple := metadata.localRouteIsSimple
    wellFormed degree isLocal valid localLiteralMember
  simpa [drawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] using simple

/-- Indexed route simplicity for the complete assembled drawing. -/
theorem drawingPlanarSATLocalIncidenceDrawing_routesAreSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).RoutesAreSimple := by
  apply
    (drawingPlanarSATLocalIncidenceDrawing formula)
      |>.routesAreSimple_of_members
  rw [drawingPlanarSATLocalIncidenceDrawing_formula,
    drawingPlanarSATLocalIncidenceDrawing_routes]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact drawingPlanarSATLocalIncidenceRoute_isSimple
    formula wellFormed degree isLocal clauseMember literalMember

/-- Complete finite planarity now reduces exactly to global separation;
route simplicity is already discharged component by component. -/
theorem drawingPlanarSATLocalIncidenceDrawing_isPlanar_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).IsPlanar ↔
      (drawingPlanarSATLocalIncidenceDrawing
        formula).GlobalSeparation := by
  exact
    (drawingPlanarSATLocalIncidenceDrawing formula)
      |>.isPlanar_iff_globalSeparation
        (drawingPlanarSATLocalIncidenceDrawing_routesAreSimple
          formula wellFormed degree isLocal)

end PeriodicOrthocrossing
end LeanTrominoes
