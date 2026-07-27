import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing

/-!
# Geometry of periodicized routed SAT variables

The finite routed SAT block explicitly names neighboring translates of route
terminals and original-variable vertices.  Periodicization removes those
translates from the protovariable names and stores them as literal offsets.

This file records the geometric counterpart of that logical normalization:
the variable vertex drawn in the finite block is exactly the canonical
periodic protovariable position translated by its stored offset.  Incidence
routes can therefore be designed in the finite block and transferred to the
periodic positioned formula without changing their physical endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Physical position of a variable vertex in the finite neighboring routed
SAT block, before its explicit translate is normalized into a periodic
literal offset. -/
def drawingPlanarSATVariablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PlanarSATVariable Variable → Cell
  | .inl (.carrier node) =>
      node.position (PeriodicCNF.incidenceGraph formula)
  | .inl (.atom occurrence) =>
      Cell.add
        (liftedIncidenceVertexMacroOrigin formula
          (.variable occurrence.1) occurrence.2)
        duplicatorArmCenterPosition
  | .inr (crossing, internal) =>
      Cell.add (crossingMacroOrigin crossing)
        (CrossoverVariable.position
          (crossoverInternalVariable internal))

/-- Normalizing a finite routed variable preserves its physical drawing
position: its explicit neighboring translate becomes exactly the periodic
literal translation. -/
theorem normalizePlanarSATVariable_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable : PlanarSATVariable Variable) :
    Cell.add
        ((drawingPeriodicPlanarSATPlacement formula).position
          (normalizePlanarSATVariable inputVariable).1)
        ((drawingPeriodicPlanarSATPlacement formula).translation
          (normalizePlanarSATVariable inputVariable).2) =
      drawingPlanarSATVariablePosition formula inputVariable := by
  let graph := PeriodicCNF.incidenceGraph formula
  cases inputVariable with
  | inl node =>
      cases node with
      | carrier carrier =>
          cases carrier with
          | boundary boundary =>
              rw [drawingPlanarSATVariablePosition]
              simp [normalizePlanarSATVariable,
                drawingPeriodicPlanarSATPlacement,
                drawingPeriodicPlanarSATVariablePosition,
                CarrierNode.position,
                PeriodicVariablePlacement.translation,
                Cell.add, Cell.scale]
          | terminal terminal =>
              rcases terminal with
                ⟨indexed, ⟨translateX, translateY⟩, endpoint⟩
              rw [drawingPlanarSATVariablePosition]
              cases endpoint <;>
                apply Prod.ext <;>
                simp [normalizePlanarSATVariable,
                  drawingPeriodicPlanarSATPlacement,
                  drawingPeriodicPlanarSATVariablePosition,
                  CarrierNode.position,
                  PeriodicVariablePlacement.translation,
                  SegmentTerminal.position,
                  SegmentTerminal.drawingPoint,
                  GridSegment.translate,
                  PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize, planarMacroScale,
                  Cell.add, Cell.scale] <;>
                ring
      | atom occurrence =>
          rcases occurrence with ⟨atom, ⟨translateX, translateY⟩⟩
          rw [drawingPlanarSATVariablePosition]
          apply Prod.ext <;>
          simp [normalizePlanarSATVariable,
            drawingPeriodicPlanarSATPlacement,
            drawingPeriodicPlanarSATVariablePosition,
            PeriodicVariablePlacement.translation,
            liftedIncidenceVertexMacroOrigin,
            liftedIncidenceVertexPosition,
            PeriodicGridDrawing.periodTranslation,
            drawing_gridSize, planarMacroScale,
            Cell.add, Cell.scale] <;>
          ring
  | inr internal =>
      rcases internal with ⟨crossing, internal⟩
      rw [drawingPlanarSATVariablePosition]
      simp [normalizePlanarSATVariable,
        drawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATVariablePosition,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale]

/-- Equivalent literal-level form of
`normalizePlanarSATVariable_position`. -/
theorem periodicizePlanarSATLiteral_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PlanarSATVariable Variable × Bool) :
    (drawingPeriodicPlanarSATPlacement formula).literalPosition
        (periodicizePlanarSATLiteral literal) =
      drawingPlanarSATVariablePosition formula literal.1 := by
  exact normalizePlanarSATVariable_position formula literal.1

/-- Translate a finite incidence polyline back from its displayed clause
translate to the canonical anchor translate used by the periodic incidence
graph. -/
def normalizePlanarSATIncidenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (route : List Cell) : List Cell :=
  let placement := drawingPeriodicPlanarSATPlacement formula
  let anchor :=
    PeriodicCNF.clauseAnchor
      (periodicizePlanarSATClause clause)
  route.map fun point =>
    Cell.sub point (placement.translation anchor)

/-- Anchor normalization sends the displayed finite clause vertex to the
canonical periodic clause protovariable position. -/
theorem normalizePlanarSATIncidenceRoute_head?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (route : List Cell)
    (routeHead : route.head? = some clause.position) :
    (normalizePlanarSATIncidenceRoute
        formula clause route).head? =
      some
        (PositionedPeriodicCNF.canonicalClausePosition
          (drawingPeriodicPlanarSATPlacement formula)
          ⟨clause.position,
            periodicizePlanarSATClause clause⟩) := by
  simp [normalizePlanarSATIncidenceRoute, routeHead,
    PositionedPeriodicCNF.canonicalClausePosition]

/-- Subtracting a clause anchor from a physical literal occurrence subtracts
that anchor from the occurrence's periodic offset. -/
theorem literalPosition_sub_anchor
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable)
    (anchor : Cell) :
    Cell.sub (placement.literalPosition literal)
        (placement.translation anchor) =
      Cell.add (placement.position literal.atom)
        (placement.translation
          (Cell.sub literal.offset anchor)) := by
  apply Prod.ext <;>
  simp [PeriodicVariablePlacement.literalPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale] <;>
  ring

/-- Anchor normalization sends a finite incidence route's variable endpoint
to the translated target used by the periodic incidence graph. -/
theorem normalizePlanarSATIncidenceRoute_getLast?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (literal : PlanarSATVariable Variable × Bool)
    (route : List Cell)
    (routeLast :
      route.getLast? =
        some
          (drawingPlanarSATVariablePosition formula literal.1)) :
    (normalizePlanarSATIncidenceRoute
        formula clause route).getLast? =
      some
        (Cell.add
          ((drawingPeriodicPlanarSATPlacement formula).position
            (periodicizePlanarSATLiteral literal).atom)
          ((drawingPeriodicPlanarSATPlacement formula).translation
            (Cell.sub
              (periodicizePlanarSATLiteral literal).offset
              (PeriodicCNF.clauseAnchor
                (periodicizePlanarSATClause clause))))) := by
  rw [← periodicizePlanarSATLiteral_position formula literal]
    at routeLast
  simp only [normalizePlanarSATIncidenceRoute,
    List.getLast?_map, routeLast, Option.map_some]
  exact congrArg some
    (literalPosition_sub_anchor
      (drawingPeriodicPlanarSATPlacement formula)
      (periodicizePlanarSATLiteral literal)
      (PeriodicCNF.clauseAnchor
        (periodicizePlanarSATClause clause)))

end PeriodicOrthocrossing
end LeanTrominoes
