/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATCornerEqualityCarrierInterface
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing
import LeanTrominoes.PlanarThreeSATRoutedClauseIncidenceDrawing

/-!
# Carrier-facing boundaries of terminal macrocell drawings

The three fanout arms at a routed clause or variable occupy the west,
north, and east compass ports of their macrocell.  Every direct incidence
inside either terminal gadget remains on the internal side of each active
carrier boundary, and every occurrence of the shared port is an advertised
route endpoint.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Compass carrier port occupied by one routed clause/variable fanout arm. -/
def DuplicatorArm.carrierPort : DuplicatorArm → CornerPort
  | .left => .west
  | .middle => .north
  | .right => .east

/-- The duplicator-arm and compass-port presentations use the same local
point. -/
@[simp] theorem DuplicatorArm.carrierPort_position
    (arm : DuplicatorArm) :
    arm.carrierPort.position = arm.portPosition := by
  cases arm <;>
    rfl

/-- Every route of one active duplicator arm remains inside the carrier
boundary at that arm's external port. -/
theorem
    duplicatorArmStraightIncidenceDrawing_routePoints_insideCarrierBoundary
    (arm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing arm).RoutePointsSatisfy
      arm.carrierPort.InsideCarrierBoundary := by
  cases arm <;>
    native_decide

/-- Contact with the external fanout port is endpoint-only in every route
of one active duplicator arm. -/
theorem
    duplicatorArmStraightIncidenceDrawing_routeContactsAt_carrierPort
    (arm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing arm).RouteContactsAtEndpoint
      arm.carrierPort.position := by
  exact
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routeContactsAtEndpoint
      (duplicatorArmFormula arm)
      (DuplicatorArmVariable.position arm)
      arm.carrierPort.position

/-- Every source-clause ray remains inside the carrier boundary at any one
of the three fanout ports. -/
theorem
    routedClausePortStraightIncidenceDrawing_routePoints_insideCarrierBoundary
    (literals : List (DuplicatorArm × Bool))
    (arm : DuplicatorArm) :
    (routedClausePortStraightIncidenceDrawing literals).RoutePointsSatisfy
      arm.carrierPort.InsideCarrierBoundary := by
  apply
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePointsSatisfy
  · intro clause clauseMember
    simp only [routedClausePortFormula,
      List.mem_singleton] at clauseMember
    subst clause
    cases arm <;>
      norm_num [DuplicatorArm.carrierPort,
        CornerPort.InsideCarrierBoundary]
  · intro clause clauseMember literal _literalMember
    simp only [routedClausePortFormula,
      List.mem_singleton] at clauseMember
    subst clause
    rcases literal with ⟨literalArm, polarity⟩
    cases arm <;> cases literalArm <;>
      norm_num [DuplicatorArm.carrierPort,
        CornerPort.InsideCarrierBoundary,
        DuplicatorArm.portPosition]

/-- Contact with any one fanout port is endpoint-only in every direct
source-clause ray. -/
theorem
    routedClausePortStraightIncidenceDrawing_routeContactsAt_carrierPort
    (literals : List (DuplicatorArm × Bool))
    (arm : DuplicatorArm) :
    (routedClausePortStraightIncidenceDrawing literals).RouteContactsAtEndpoint
      arm.carrierPort.position := by
  exact
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routeContactsAtEndpoint
      (routedClausePortFormula literals)
      DuplicatorArm.portPosition
      arm.carrierPort.position

/-- Translating an active duplicator arm places its internal carrier
boundary at the translated macrocell origin. -/
theorem
    duplicatorArmStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
    (arm : DuplicatorArm) (origin : Cell) :
    ((duplicatorArmStraightIncidenceDrawing arm).translate origin).RoutePointsSatisfy
        (arm.carrierPort.InsideCarrierBoundaryAt origin) := by
  exact
    (duplicatorArmStraightIncidenceDrawing_routePoints_insideCarrierBoundary
      arm).translate origin
        (fun point inside =>
          arm.carrierPort.insideCarrierBoundaryAt_add
            origin point inside)

/-- Translation carries endpoint-only arm contact to the absolute fanout
port. -/
theorem
    duplicatorArmStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
    (arm : DuplicatorArm) (origin : Cell) :
    ((duplicatorArmStraightIncidenceDrawing arm).translate origin).RouteContactsAtEndpoint
        (Cell.add origin arm.carrierPort.position) := by
  exact
    (duplicatorArmStraightIncidenceDrawing_routeContactsAt_carrierPort
      arm).translate origin

/-- Translating a source-clause star places its internal carrier boundary
at the translated macrocell origin. -/
theorem
    routedClausePortStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
    (literals : List (DuplicatorArm × Bool))
    (arm : DuplicatorArm) (origin : Cell) :
    ((routedClausePortStraightIncidenceDrawing literals).translate origin).RoutePointsSatisfy
        (arm.carrierPort.InsideCarrierBoundaryAt origin) := by
  exact
    (routedClausePortStraightIncidenceDrawing_routePoints_insideCarrierBoundary
      literals arm).translate origin
        (fun point inside =>
          arm.carrierPort.insideCarrierBoundaryAt_add
            origin point inside)

/-- Translation carries endpoint-only source-clause contact to the absolute
fanout port. -/
theorem
    routedClausePortStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
    (literals : List (DuplicatorArm × Bool))
    (arm : DuplicatorArm) (origin : Cell) :
    ((routedClausePortStraightIncidenceDrawing literals).translate origin).RouteContactsAtEndpoint
        (Cell.add origin arm.carrierPort.position) := by
  exact
    (routedClausePortStraightIncidenceDrawing_routeContactsAt_carrierPort
      literals arm).translate origin

end PlanarThreeSAT
end LeanTrominoes
