/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATIncidencePlanarity
import LeanTrominoes.PlanarThreeSATCornerEqualityCarrierInterface
import LeanTrominoes.PeriodicOrthocrossingPlanarWires

/-!
# Carrier-facing boundaries of the crossover drawing

The four external variables of the fixed crossover template occupy the
standard west, east, south, and north carrier ports.  Every direct incidence
route stays on the internal side of each of these boundaries and meets the
corresponding port only at a route endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The carrier port occupied by one external side of the crossover. -/
def CrossingSide.carrierPort : CrossingSide → CornerPort
  | .left => .west
  | .right => .east
  | .top => .south
  | .bottom => .north

@[simp] theorem CrossingSide.carrierPort_position
    (side : CrossingSide) :
    side.carrierPort.position = side.localPosition := by
  cases side <;>
    rfl

/-- Every direct incidence route of the fixed crossover stays on the
internal side of each carrier-facing boundary. -/
theorem
    crossoverStraightIncidenceDrawing_routePoints_insideCarrierBoundary
    (side : CrossingSide) :
    crossoverStraightIncidenceDrawing.RoutePointsSatisfy
      side.carrierPort.InsideCarrierBoundary := by
  cases side <;>
    apply
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePointsSatisfy
      crossoverFormula CrossoverVariable.position
  all_goals native_decide

/-- The fixed crossover has endpoint-only contact with each of its four
carrier ports. -/
theorem crossoverStraightIncidenceDrawing_routeContactsAt_carrierPort
    (side : CrossingSide) :
    crossoverStraightIncidenceDrawing.RouteContactsAtEndpoint
      side.carrierPort.position := by
  exact
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routeContactsAtEndpoint
    crossoverFormula CrossoverVariable.position
    side.carrierPort.position

/-- Translation transports the crossover's internal boundary certificate
to an arbitrary macrocell origin. -/
theorem
    crossoverStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
    (side : CrossingSide) (origin : Cell) :
    (crossoverStraightIncidenceDrawing.translate
      origin).RoutePointsSatisfy
        (side.carrierPort.InsideCarrierBoundaryAt origin) := by
  exact
    (crossoverStraightIncidenceDrawing_routePoints_insideCarrierBoundary
      side).translate origin
      (fun point inside =>
        side.carrierPort.insideCarrierBoundaryAt_add
          origin point inside)

/-- Translation transports endpoint-only contact to the physical crossover
port. -/
theorem
    crossoverStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
    (side : CrossingSide) (origin : Cell) :
    (crossoverStraightIncidenceDrawing.translate
      origin).RouteContactsAtEndpoint
        (Cell.add origin side.carrierPort.position) := by
  exact
    (crossoverStraightIncidenceDrawing_routeContactsAt_carrierPort
      side).translate origin

end PeriodicOrthocrossing
end LeanTrominoes
