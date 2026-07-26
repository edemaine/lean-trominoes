import LeanTrominoes.LocalIncidenceDrawing
import LeanTrominoes.PlanarThreeDMVariableOccurrenceGadget

/-!
# Certified local drawings of the planar 3DM connectors

This file turns the combinatorial coordinates of the ordinary fixed-green,
ordinary fixed-blue, and fixed-red occurrence modules into explicit
orthogonal incidence drawings.  The three connector elements are treated as
temporary boundary vertices; the global construction will extend their
incident routes along the corresponding source incidence route.

The few diagonal incidences in the displayed gadget coordinates are routed
around the outside of the local box.  All endpoint, orthogonality, and exact
continuous nonintersection conditions are discharged by finite computation.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

open Gadget

namespace VariableOccurrence

/-- A direct one-segment route. -/
def directRoute (start finish : Cell) : List Cell :=
  [start, finish]

/-- The one routed connector incidence that cannot be drawn directly in an
ordinary occurrence module. -/
def outerConnectorRoute
    (variant : VariableOccurrenceVariant) : List Cell :=
  match variant with
  | .fixedGreen =>
      [(0, 0), (0, -4), (8, -4), (8, 6), (4, 6)]
  | .fixedBlue =>
      [(0, 0), (0, -4), (8, -4), (8, 4), (6, 4)]

/-- The unified reference selected by one color. -/
def reference (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple) :
    WireColor → VariableOccurrenceElement
  | .red => (triple.references variant).red
  | .green => (triple.references variant).green
  | .blue => (triple.references variant).blue

/-- Orthogonal route for one colored incidence of an ordinary occurrence
module. -/
def route (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple)
    (color : WireColor) : List Cell :=
  if triple = .first ∧ color = variant.fixedColor then
    outerConnectorRoute variant
  else
    directRoute triple.position
      (reference variant triple color).position

/-- Complete local drawing of either ordinary occurrence connector. -/
def drawing (variant : VariableOccurrenceVariant) :
    LocalIncidenceDrawing
      VariableOccurrenceTriple VariableOccurrenceElement where
  triplePosition := VariableOccurrenceTriple.position
  elementPosition := VariableOccurrenceElement.position
  reference := reference variant
  route := route variant

/-- Both ordinary occurrence variants have certified planar orthogonal
drawings with the advertised incidence endpoints. -/
theorem drawing_isValid (variant : VariableOccurrenceVariant) :
    (drawing variant).IsValid := by
  cases variant <;> native_decide

end VariableOccurrence

/-- Unified colored elements of the fixed-red connector drawing. -/
inductive FixedRedConnectorElement
  | red (element : FixedRedConnectorRed)
  | green (element : FixedRedConnectorGreen)
  | blue (element : FixedRedConnectorBlue)
  deriving DecidableEq, Repr

instance : Fintype FixedRedConnectorElement :=
  Fintype.ofList
    [.red .leftTopPort, .red .leftBottomPort,
      .red .middleRung, .red .topAuxiliary, .red .connectorPort,
      .green .leftRung, .green .topRightLink,
      .green .bottomRightLink, .green .connectorPort,
      .blue .topLeftLink, .blue .bottomLeftLink,
      .blue .rightRung, .blue .connectorPort] (by
        intro element
        cases element with
        | red red => cases red <;> simp
        | green green => cases green <;> simp
        | blue blue => cases blue <;> simp)

namespace FixedRedConnectorElement

/-- Position inherited from the corresponding colored element family. -/
def position : FixedRedConnectorElement → Cell
  | .red element => element.position
  | .green element => element.position
  | .blue element => element.position

end FixedRedConnectorElement

namespace FixedRedConnector

/-- Unified colored reference of a fixed-red connector triple. -/
def reference (triple : FixedRedConnectorTriple) :
    WireColor → FixedRedConnectorElement
  | .red => .red triple.references.red
  | .green => .green triple.references.green
  | .blue => .blue triple.references.blue

/-- The two short fanout routes from the auxiliary triple to its green and
blue connector ports. -/
def auxiliaryConnectorRoute : WireColor → List Cell
  | .green => [(12, 0), (12, -2), (14, -2), (14, -1)]
  | .blue => [(12, 0), (13, 0), (13, 1), (14, 1)]
  | .red => [(12, 0), (10, 0)]

/-- Orthogonal route for one colored fixed-red connector incidence. -/
def route (triple : FixedRedConnectorTriple)
    (color : WireColor) : List Cell :=
  if triple = .auxiliary then
    auxiliaryConnectorRoute color
  else
    VariableOccurrence.directRoute triple.position
      (FixedRedConnectorElement.position (reference triple color))

/-- Complete local drawing of the fixed-red occurrence connector. -/
def drawing :
    LocalIncidenceDrawing
      FixedRedConnectorTriple FixedRedConnectorElement where
  triplePosition := FixedRedConnectorTriple.position
  elementPosition := FixedRedConnectorElement.position
  reference := reference
  route := route

/-- The fixed-red detour has a certified planar orthogonal drawing with the
advertised incidence endpoints. -/
theorem drawing_isValid : drawing.IsValid := by
  native_decide

end FixedRedConnector

end PlanarThreeDM
end LeanTrominoes
