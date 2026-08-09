import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates

/-!
# Fixed-green normalized contact repair

Polarity normalization uses a fixed-green connector in the true orientation.
The lane-aligned occurrence-tree rotation places its blue, red, and green
leaves directly at the three physical ribbon lanes.  This file records the
finite endpoint-aware certificate that replaced the former local-contact
obstruction.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The one-module connector-kind data for the normalized fixed-green
occurrence. -/
def fixedGreenTrueKind (_ : VariableSiteSlot) : VariableConnectorKind :=
  .fixedGreen

/-- The normalized fixed-green polarity data. -/
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

/-- Every core incidence in the normalized fixed-green module has complete
endpoint-aware separation from every local gate. -/
theorem fixedGreenTrue_core_gate_endpointSeparated :
    ∀ (triple : VariableOccurrenceTriple)
      (routeColor gateColor : WireColor),
      RoutesAvoidEachOther
          (fixedGreenTrueCoreRoute triple routeColor)
          (fixedGreenTrueGateRoute gateColor) := by
  native_decide

/-- The endpoint-aware certificate contains the three continuous-planarity
conditions. -/
theorem fixedGreenTrue_core_gate_avoidInteriorContacts :
    ∀ (triple : VariableOccurrenceTriple)
      (routeColor gateColor : WireColor),
      RoutesAvoidInteriorContacts
        (fixedGreenTrueCoreRoute triple routeColor)
        (fixedGreenTrueGateRoute gateColor) := by
  intro triple routeColor gateColor
  exact RoutesAvoidEachOther.toRoutesAvoidInteriorContacts
    (fixedGreenTrue_core_gate_endpointSeparated
      triple routeColor gateColor)

/-- The routed blue incidence meets its gate only at the advertised splice
port. -/
theorem fixedGreenTrue_blue_commonPoints :
    (fixedGreenTrueCoreRoute .first .blue).filter
        (fun point => point ∈ fixedGreenTrueGateRoute .blue) =
      [(20, 76)] := by
  native_decide

/-- The routed red incidence meets its gate only at its splice port. -/
theorem fixedGreenTrue_red_commonPoints :
    (fixedGreenTrueCoreRoute .auxiliary .red).filter
        (fun point => point ∈ fixedGreenTrueGateRoute .red) =
      [(24, 76)] := by
  native_decide

/-- The routed green incidence meets its gate only at its splice port. -/
theorem fixedGreenTrue_green_commonPoints :
    (fixedGreenTrueCoreRoute .auxiliary .green).filter
        (fun point => point ∈ fixedGreenTrueGateRoute .green) =
      [(28, 76)] := by
  native_decide

/-- The repaired normalized fixed-green table is one of the endpoint-clear
tables admitted by the global routing interface. -/
theorem fixedGreenTrue_localGateTableEndpointClear :
    VariableLocalGateTableEndpointClear .fixedGreen true := by
  decide

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
