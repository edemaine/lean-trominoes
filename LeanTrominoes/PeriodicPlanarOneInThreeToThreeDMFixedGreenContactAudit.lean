import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates

/-!
# The fixed-green local-contact obstruction

Polarity normalization leaves one variable connector outside the two
endpoint-clear local tables: a fixed-green connector in the true
orientation.  This file records the exact finite obstruction.  Its green
gate route passes through the common endpoint `(36, 68)` of the second and
auxiliary green core incidences.  Thus the continuous-interior certificate
still holds, but endpoint-only route contact does not.

The obstruction is deliberately isolated before replacing this one
module-local route by the required site-wide annular route.  In particular,
the audit prevents a later global collision proof from silently treating
continuous planarity as endpoint-only contact.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The one-module connector-kind data for the exceptional normalized
fixed-green occurrence. -/
def fixedGreenTrueKind (_ : VariableSiteSlot) : VariableConnectorKind :=
  .fixedGreen

/-- The exceptional normalized polarity data. -/
def fixedGreenTruePolarity (_ : VariableSiteSlot) : Bool :=
  true

/-- Any of the three triples in the one-module fixed-green site. -/
def fixedGreenTrueActiveTriple
    (triple : VariableOccurrenceTriple) :
    ActiveVariableSiteTriple 1 fixedGreenTrueKind :=
  ⟨.ordinary .first .fixedGreen triple, by
    cases triple <;>
      simp [VariableSiteTriple.MatchesKind,
        fixedGreenTrueKind, VariableSiteSlot.index]⟩

/-- One core incidence in standard ribbon-macrocell coordinates. -/
def fixedGreenTrueCoreRoute
    (triple : VariableOccurrenceTriple)
    (color : WireColor) : List Cell :=
  translatePolyline standardThreeStrandLayout.variableOffset
    ((variableSiteDrawing 1 fixedGreenTrueKind fixedGreenTruePolarity).route
      (fixedGreenTrueActiveTriple triple) color)

/-- One connector gate in standard ribbon-macrocell coordinates. -/
def fixedGreenTrueGateRoute (color : WireColor) : List Cell :=
  standardVariableLocalGateRoute
    .first .fixedGreen true color

/-- The only endpoint-aware failures between a fixed-green/true module's
core and its local gates are the two green incidences ending at the shared
green element. -/
theorem fixedGreenTrue_core_gate_endpointContact_classification :
    ∀ (triple : VariableOccurrenceTriple)
      (routeColor gateColor : WireColor),
      RoutesAvoidEachOther
          (fixedGreenTrueCoreRoute triple routeColor)
          (fixedGreenTrueGateRoute gateColor) ↔
        ¬(routeColor = .green ∧ gateColor = .green ∧
          (triple = .second ∨ triple = .auxiliary)) := by
  native_decide

/-- Even the exceptional two pairs retain the three conditions needed for
continuous planarity: segment interiors are disjoint and neither route has
a listed point in the other route's segment interior. -/
theorem fixedGreenTrue_core_gate_avoidInteriorContacts :
    ∀ (triple : VariableOccurrenceTriple)
      (routeColor gateColor : WireColor),
      RoutesAvoidInteriorContacts
        (fixedGreenTrueCoreRoute triple routeColor)
        (fixedGreenTrueGateRoute gateColor) := by
  native_decide

/-- The second green core route and the green gate have exactly one common
listed point. -/
theorem fixedGreenTrue_second_green_commonPoints :
    (fixedGreenTrueCoreRoute .second .green).filter
        (fun point => point ∈ fixedGreenTrueGateRoute .green) =
      [(36, 68)] := by
  native_decide

/-- The auxiliary green core route has the same unique contact. -/
theorem fixedGreenTrue_auxiliary_green_commonPoints :
    (fixedGreenTrueCoreRoute .auxiliary .green).filter
        (fun point => point ∈ fixedGreenTrueGateRoute .green) =
      [(36, 68)] := by
  native_decide

/-- The common point is not an endpoint of the complete green gate route,
which is why ordinary endpoint-permitting separation rejects the contact. -/
theorem fixedGreenTrue_contact_not_gate_endpoint :
    (fixedGreenTrueGateRoute .green).head? = some (24, 72) ∧
      (fixedGreenTrueGateRoute .green).getLast? = some (28, 108) ∧
      (36, 68) ≠ (24, 72) ∧
      (36, 68) ≠ (28, 108) := by
  native_decide

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
