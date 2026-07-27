import LeanTrominoes.PeriodicOrthocrossingCrossoverIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingCrossoverCarrierInterface

/-!
# Carrier interfaces of placed crossover components

Translation and logical scoping preserve all four internal carrier-boundary
and endpoint-contact certificates of the fixed crossover drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every route of a placed crossover remains inside the carrier boundary
at any one of its four external sides. -/
theorem
    drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (side : CrossingSide) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RoutePointsSatisfy
        (side.carrierPort.InsideCarrierBoundaryAt
          (crossingMacroOrigin crossing)) := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
  exact
    (crossoverStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
      side (crossingMacroOrigin crossing)).rename _ _

/-- A placed crossover has endpoint-only contact with each physical
carrier port. -/
theorem
    drawingPlanarSATCrossoverIncidenceDrawing_routeContactsAt_carrierPort
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (side : CrossingSide) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RouteContactsAtEndpoint
        (Cell.add
          (crossingMacroOrigin crossing)
          side.carrierPort.position) := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
  exact
    (crossoverStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
      side (crossingMacroOrigin crossing)).rename _ _

end PeriodicOrthocrossing
end LeanTrominoes
