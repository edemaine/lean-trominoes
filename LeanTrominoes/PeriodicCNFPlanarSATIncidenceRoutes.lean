import LeanTrominoes.PeriodicCNFPlanarSATDeduplication
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicThreeSATThreeAngularOrder

/-!
# Incidence routes for the deduplicated routed SAT source

The routed planar SAT construction is first a finite list of embedded
clauses.  This file states the raw geometric obligation on a route family in
that finite presentation order and transports it through periodicization,
opaque variable wrapping, clause-orbit deduplication, and anchor
normalization.

Thus future gadget-specific routing only needs to connect each displayed
finite clause to the displayed physical position of each of its literals.
All periodic indexing and endpoint compatibility are handled here.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Raw endpoint condition for routes indexed by the finite routed planar SAT
formula before periodicization. -/
def DrawingPlanarSATPhysicalIncidenceRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  EmbeddedPhysicalIncidenceRoutesMatch
    (drawingPlanarSATFormula formula)
    (drawingPlanarSATVariablePosition formula) routes

/-- Direct physical incidences in the finite routed SAT block.  These
straight terminal rays need not yet be orthogonal: their purpose is to retain
the full cyclic order at variables whose degree can exceed four before
occurrence splitting. -/
def drawingPlanarSATStraightIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  straightIncidenceRoutes
    (drawingPlanarSATFormula formula)
    (drawingPlanarSATVariablePosition formula)

/-- Every genuine direct routed-SAT incidence has its exact finite physical
endpoints. -/
theorem drawingPlanarSATStraightIncidenceRoutes_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATPhysicalIncidenceRoutesMatch
      formula (drawingPlanarSATStraightIncidenceRoutes formula) := by
  exact straightIncidenceRoutes_physicalRoutesMatch
    (drawingPlanarSATFormula formula)
    (drawingPlanarSATVariablePosition formula)

/-- Periodicizing an arbitrary finite planar-SAT formula preserves a raw
route family's physical endpoints whenever the placement realizes the
literal periodicization at the same points. -/
theorem positionPeriodicizedPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*}
    (finiteFormula :
      List (EmbeddedClause (PlanarSATVariable Variable)))
    (variablePosition : PlanarSATVariable Variable → Cell)
    (placement :
      PeriodicVariablePlacement
        (PeriodicPlanarSATVariable Variable))
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (routesMatch :
      EmbeddedPhysicalIncidenceRoutesMatch
        finiteFormula variablePosition routes)
    (literalPositionsMatch :
      ∀ literal,
        placement.literalPosition
            (periodicizePlanarSATLiteral literal) =
          variablePosition literal.1) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (positionPeriodicizedPlanarSATFormula finiteFormula)
      placement routes := by
  intro positionedClause clauseIndex positionedClauseMember
    periodicLiteral literalIndex periodicLiteralMember
  change
    (positionedClause, clauseIndex) ∈
      (finiteFormula.map fun clause =>
        ⟨clause.position,
          periodicizePlanarSATClause clause⟩).zipIdx
    at positionedClauseMember
  rw [List.zipIdx_map] at positionedClauseMember
  rcases List.mem_map.mp positionedClauseMember with
    ⟨taggedClause, taggedClauseMember,
      positionedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd positionedClauseEqual
  have positionedClauseValueEqual :
      positionedClause =
        ⟨taggedClause.1.position,
          periodicizePlanarSATClause taggedClause.1⟩ := by
    exact (congrArg Prod.fst positionedClauseEqual).symm
  subst clauseIndex
  subst positionedClause
  change
    (periodicLiteral, literalIndex) ∈
      (taggedClause.1.literals.map
        periodicizePlanarSATLiteral).zipIdx
    at periodicLiteralMember
  rw [List.zipIdx_map] at periodicLiteralMember
  rcases List.mem_map.mp periodicLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember,
      periodicLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd periodicLiteralEqual
  have periodicLiteralValueEqual :
      periodicLiteral =
        periodicizePlanarSATLiteral taggedLiteral.1 := by
    exact (congrArg Prod.fst periodicLiteralEqual).symm
  subst literalIndex
  subst periodicLiteral
  have endpoints :=
    routesMatch taggedClause.1 taggedClause.2
      taggedClauseMember taggedLiteral.1 taggedLiteral.2
      taggedLiteralMember
  refine ⟨endpoints.1, ?_⟩
  rw [endpoints.2]
  exact congrArg some
    (literalPositionsMatch taggedLiteral.1).symm

/-- The finite endpoint condition becomes the generic physical endpoint
condition on the positioned periodicization, with unchanged indices. -/
theorem drawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (routesMatch :
      DrawingPlanarSATPhysicalIncidenceRoutesMatch formula routes) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (drawingPositionedPeriodicPlanarSATFormula formula)
      (drawingPeriodicPlanarSATPlacement formula) routes := by
  exact
    positionPeriodicizedPlanarSATFormula_physicalRoutesMatch
      (drawingPlanarSATFormula formula)
      (drawingPlanarSATVariablePosition formula)
      (drawingPeriodicPlanarSATPlacement formula)
      routes routesMatch
      (periodicizePlanarSATLiteral_position formula)

/-- Raw routes also match the opaque wrapped positioned source, because the
wrapper changes neither physical positions nor the drawing period. -/
theorem wrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (routesMatch :
      DrawingPlanarSATPhysicalIncidenceRoutesMatch formula routes) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula) routes := by
  apply
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch.rename
      (drawingPositionedPeriodicPlanarSATFormula formula)
      (drawingPeriodicPlanarSATPlacement formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      routes WrappedPeriodicVariable.mk
      (drawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
        formula routes routesMatch)
  · intro atom
    rfl
  · rfl

/-- The actual canonical route family consumed by the geometry-ordered
pipeline: finite wrapped routes, reindexed through clause-orbit
deduplication and normalized by each retained clause anchor. -/
def deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.deduplicatedIncidenceRoutes
    (anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula) routes)

/-- Canonical periodic routes obtained from the direct finite terminal rays
after wrapping, clause-orbit deduplication, and anchor normalization. -/
def deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    formula (drawingPlanarSATStraightIncidenceRoutes formula)

/-- Lawful cyclic occurrence order of the unsplit routed SAT source,
computed from full terminal-ray polar angles. -/
def drawingAngularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicThreeSATThree.OccurrenceOrder
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase :=
  PeriodicThreeSATThree.angularOccurrenceOrder
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)

/-- Every genuine incidence in the deduplicated wrapped source retrieves the
canonical normalized route with its exact periodic endpoints. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (routesMatch :
      DrawingPlanarSATPhysicalIncidenceRoutesMatch formula routes)
    {tagged :
      CNFIncidence (WrappedPeriodicPlanarSATVariable Variable) × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata
          (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase).zipIdx) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula routes
        tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula)
            (wrappedDrawingPeriodicPlanarSATPlacement formula)
            (.clause tagged.1.clauseIndex)) ∧
      (deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula routes
          tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            ((wrappedDrawingPeriodicPlanarSATPlacement formula).position
              tagged.1.literal.atom)
            ((wrappedDrawingPeriodicPlanarSATPlacement formula).translation
              tagged.1.edge.offset)) := by
  exact
    PositionedPeriodicCNF.deduplicatedIncidenceRoutes_endpoints_of_tagged
        (anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)
        (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
          (wrappedDrawingPeriodicPlanarSATPlacement formula) routes)
        (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_physicalRoutesMatch
            (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
            (wrappedDrawingPeriodicPlanarSATPlacement formula)
            routes
            (wrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
              formula routes routesMatch))
        taggedMember

/-- The specialized transported routes satisfy the complete periodic
incidence-graph endpoint condition. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (routesMatch :
      DrawingPlanarSATPhysicalIncidenceRoutesMatch formula routes) :
    (PositionedPeriodicCNF.incidenceDrawing
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula routes)).RoutesMatch
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceGraph := by
  apply
    PositionedPeriodicCNF.deduplicatedIncidenceDrawing_routesMatch
      (anchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
        (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula) routes)
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_physicalRoutesMatch
          (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
          (wrappedDrawingPeriodicPlanarSATPlacement formula)
          routes
          (wrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
            formula routes routesMatch))
  change
    0 <
      planarMacroScale.toNat *
        drawingGridSize (PeriodicCNF.incidenceGraph formula)
  exact Nat.mul_pos
    (by norm_num [planarMacroScale])
    (drawingGridSize_pos
      (PeriodicCNF.incidenceGraph formula))

/-- The concrete normalized direct-ray family satisfies the complete
periodic endpoint condition without any remaining route premise. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
        formula)).RoutesMatch
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceGraph := by
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
      formula
      (drawingPlanarSATStraightIncidenceRoutes formula)
      (drawingPlanarSATStraightIncidenceRoutes_physicalRoutesMatch
        formula)

end PeriodicOrthocrossing
end LeanTrominoes
