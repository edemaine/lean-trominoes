import LeanTrominoes.PeriodicOrthocrossingRoutedClauseIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableIncidenceDrawing
import LeanTrominoes.PlanarThreeSATTerminalCarrierInterface

/-!
# Carrier interfaces of placed terminal components

The routed-variable arm and routed-clause star adapters preserve the local
terminal templates' internal carrier-boundary and endpoint-contact
certificates in the final planar-SAT variable type.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every route of a placed active routed-variable arm remains inside the
carrier boundary at that arm's external port. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutePointsSatisfy
        (arm.carrierPort.InsideCarrierBoundaryAt
          (routedVariableOrigin formula site)) := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  exact
    (duplicatorArmStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
      arm (routedVariableOrigin formula site)).rename _ _

/-- The placed active arm has endpoint-only contact with its external
carrier port. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPort
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RouteContactsAtEndpoint
        (Cell.add
          (routedVariableOrigin formula site)
          arm.carrierPort.position) := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  exact
    (duplicatorArmStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
      arm (routedVariableOrigin formula site)).rename _ _

/-- Every route of a placed routed source clause remains inside the carrier
boundary at any one of its three possible fanout ports. -/
theorem
    drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (arm : DuplicatorArm) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutePointsSatisfy
        (arm.carrierPort.InsideCarrierBoundaryAt
          (routedClauseOrigin formula site)) := by
  let source :=
    drawingPlanarSATRoutedClauseIncidenceDrawing formula site
  let variableMap :=
    @planarSATRoutedClauseArm Variable
  let targetPosition :=
    routedClauseArmPosition formula site
  have renamedBounded :
      (source.rename variableMap targetPosition).RoutePointsSatisfy
        (arm.carrierPort.InsideCarrierBoundaryAt
          (routedClauseOrigin formula site)) := by
    rw [show source.rename variableMap targetPosition =
        (routedClausePortStraightIncidenceDrawing
          (routedClausePortLiterals formula site)).translate
            (routedClauseOrigin formula site) by
      exact drawingPlanarSATRoutedClauseIncidenceDrawing_rename
        formula site]
    exact
      routedClausePortStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundary
        (routedClausePortLiterals formula site)
        arm (routedClauseOrigin formula site)
  exact renamedBounded.of_rename variableMap targetPosition

/-- The placed routed source clause has endpoint-only contact with any one
of its three possible fanout ports. -/
theorem
    drawingPlanarSATRoutedClauseIncidenceDrawing_routeContactsAt_carrierPort
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (arm : DuplicatorArm) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RouteContactsAtEndpoint
        (Cell.add
          (routedClauseOrigin formula site)
          arm.carrierPort.position) := by
  let source :=
    drawingPlanarSATRoutedClauseIncidenceDrawing formula site
  let variableMap :=
    @planarSATRoutedClauseArm Variable
  let targetPosition :=
    routedClauseArmPosition formula site
  have renamedContacts :
      (source.rename variableMap targetPosition).RouteContactsAtEndpoint
        (Cell.add
          (routedClauseOrigin formula site)
          arm.carrierPort.position) := by
    rw [show source.rename variableMap targetPosition =
        (routedClausePortStraightIncidenceDrawing
          (routedClausePortLiterals formula site)).translate
            (routedClauseOrigin formula site) by
      exact drawingPlanarSATRoutedClauseIncidenceDrawing_rename
        formula site]
    exact
      routedClausePortStraightIncidenceDrawing_translate_routeContactsAt_carrierPort
        (routedClausePortLiterals formula site)
        arm (routedClauseOrigin formula site)
  exact renamedContacts.of_rename variableMap targetPosition

end PeriodicOrthocrossing
end LeanTrominoes
