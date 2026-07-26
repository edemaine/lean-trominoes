import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.OccurrenceSplitRingCycleDrawing

/-!
# Certified Figure 7 cycles inside positioned occurrence splitting

This module identifies each atom's appended implication clauses with the
standalone Figure 7 cycle drawing.  The correspondence is definitional:
translate the local coordinates by the atom's macrocell origin and rename
each compass `Port` to the corresponding fixed occurrence copy.

Consequently the translated local routes carry the complete finite
endpoint, orthogonality, and continuous-planarity certificate at every
input-dependent atom position.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Translate and rename one local Figure 7 implication clause. -/
def positionedLocalCycleClause
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (clause : EmbeddedClause Port) :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable) where
  position :=
    Cell.add
      (macroOrigin sourcePlacement atom) clause.position
  literals := periodicCycleClause atom clause

/-- One atom's positioned implication clauses are exactly the translated,
renamed local cycle template. -/
theorem cycleClausesFor_eq_cycleFormula
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    cycleClausesFor sourcePlacement atom =
      cycleFormula.map
        (positionedLocalCycleClause
          sourcePlacement atom) := by
  rfl

/-- The certified translated local routes used for one atom's cycle block. -/
def positionedCycleRoutes
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    (translatedCycleDrawing
      (macroOrigin sourcePlacement atom)).routes
        clauseIndex literalIndex

/-- Every per-atom cycle route family inherits the complete local
certificate. -/
theorem positionedCycleDrawing_isValid
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (translatedCycleDrawing
      (macroOrigin sourcePlacement atom)).IsValid :=
  translatedCycleDrawing_isValid _

/-- The refined placement of a fixed copy agrees with the translated local
cycle drawing's variable vertex. -/
theorem placement_copy_eq_translatedCycleVariablePosition
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (port : Port) :
    (placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.copy atom port) =
      (translatedCycleDrawing
        (macroOrigin sourcePlacement atom)).variablePosition
          port := by
  cases port <;>
    rfl

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
