import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation

/-!
# Simplicity of retained angular occurrence suffixes

Every coordinated retained route ends with one of the eight explicit
Figure 7 spokes.  The finite local spokes are simple; positioning and positive
uniform scaling preserve that property.  This supplies the terminal endpoint
isolation needed when larger inherited route splices are normalized.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Every one of the eight local Figure 7 spoke routes is geometrically
simple. -/
theorem spokeRoute_isSimple (port : Port) :
    LocalIncidenceDrawing.RouteIsSimple (spokeRoute port) := by
  cases port <;> native_decide

/-- Positioning a local Figure 7 spoke at its variable macrocell preserves
simplicity. -/
theorem angularFanSpokeRoute_isSimple
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    LocalIncidenceDrawing.RouteIsSimple
      (angularFanSpokeRoute sourcePlacement atom index) := by
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
  exact spokeRoute_isSimple (angularPortOfIndex index)

/-- Periodically translating a positioned Figure 7 spoke preserves
simplicity. -/
theorem angularFanSpokeRouteAt_isSimple
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    LocalIncidenceDrawing.RouteIsSimple
      (angularFanSpokeRouteAt sourcePlacement
        atom logicalOffset index) := by
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
  exact angularFanSpokeRoute_isSimple sourcePlacement atom index

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Every canonical angular occurrence suffix is geometrically simple. -/
theorem angularOccurrenceSuffix_isSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    LocalIncidenceDrawing.RouteIsSimple
      (angularOccurrenceSuffix sourcePlacement order
        clause literal clauseIndex literalIndex) := by
  exact
    angularFanSpokeRouteAt_isSimple
      sourcePlacement literal.atom
      (incidenceRelativeOffset clause literal)
      (angularOccurrenceIndex order literal
        clauseIndex literalIndex)

/-- Positive uniform scaling preserves simplicity of every angular
occurrence suffix. -/
theorem scalePolyline_angularOccurrenceSuffix_isSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    {factor : Nat} (factorPositive : 0 < factor) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline factor
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex)) := by
  exact
    routeIsSimple_scalePolyline
      (by exact_mod_cast factorPositive)
      (angularOccurrenceSuffix_isSimple
        sourcePlacement order clause literal
        clauseIndex literalIndex)

/-- The variable endpoint of a positively scaled angular occurrence suffix
is isolated after unit subdivision. -/
theorem scalePolyline_angularOccurrenceSuffix_lastNotInDropLast
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    {factor : Nat} (factorPositive : 0 < factor) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (scalePolyline factor
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex))) := by
  apply
    AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
  · exact
      (angularOccurrenceSuffix_orthogonal
        sourcePlacement order clause literal
        clauseIndex literalIndex).scalePolyline factorPositive
  · exact
      scalePolyline_angularOccurrenceSuffix_isSimple
        sourcePlacement order clause literal
        clauseIndex literalIndex factorPositive

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
