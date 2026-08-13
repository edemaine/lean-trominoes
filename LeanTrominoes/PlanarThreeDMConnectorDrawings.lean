/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- Clockwise quarter turn of the integer grid. -/
def rotateClockwise (point : Cell) : Cell :=
  (point.2, -point.1)

/-- Reflection across the horizontal line with the given ordinate. -/
def reflectAcrossHorizontal (axis : Int) (point : Cell) : Cell :=
  (point.1, 2 * axis - point.2)

/-- Reflection across the vertical line with the given abscissa. -/
def reflectAcrossVertical (axis : Int) (point : Cell) : Cell :=
  (2 * axis - point.1, point.2)

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
      [(0, 0), (0, -4), (8, -4), (8, 4), (6, 4)]
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

/-- Rotate an ordinary module so that its continuation ports lie on one
vertical boundary.  Positive polarity additionally reflects it so the port
for the current slot is always above the port for the next slot. -/
def orientedDrawing (variant : VariableOccurrenceVariant)
    (polarity : Bool) :
    LocalIncidenceDrawing
      VariableOccurrenceTriple VariableOccurrenceElement :=
  let rotated := (drawing variant).mapPoints rotateClockwise
  if polarity then
    rotated.mapPoints (reflectAcrossHorizontal (-2))
  else
    rotated

@[simp]
theorem orientedDrawing_reference
    (variant : VariableOccurrenceVariant) (polarity : Bool)
    (triple : VariableOccurrenceTriple) (color : WireColor) :
    (orientedDrawing variant polarity).reference triple color =
      reference variant triple color := by
  cases polarity <;> rfl

/-- The cycle triple incident to the current occurrence slot. -/
def slotContinuationTriple
    (polarity : Bool) : VariableOccurrenceTriple :=
  if polarity then .first else .second

/-- The cycle triple incident to the next used occurrence slot. -/
def nextContinuationTriple
    (polarity : Bool) : VariableOccurrenceTriple :=
  if polarity then .second else .first

/-- In the oriented ordinary template, the current-slot continuation has a
fixed upper boundary position. -/
@[simp]
theorem orientedDrawing_slotContinuationPosition
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedDrawing variant polarity).elementPosition
        (reference variant
          (slotContinuationTriple polarity) .red) =
      (0, -6) := by
  cases variant <;> cases polarity <;> native_decide

/-- The next-slot continuation has a fixed lower boundary position. -/
@[simp]
theorem orientedDrawing_nextContinuationPosition
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedDrawing variant polarity).elementPosition
        (reference variant
          (nextContinuationTriple polarity) .red) =
      (0, 2) := by
  cases variant <;> cases polarity <;> native_decide

/-- Rotation and the polarity-dependent reflection preserve the complete
ordinary-module drawing certificate. -/
theorem orientedDrawing_isValid
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedDrawing variant polarity).IsValid := by
  cases variant <;> cases polarity <;> native_decide

/-! ## Outer-face boundary template -/

/-- Triple positions in a path-shaped outer-face embedding of the ordinary
module. -/
def boundaryTriplePosition : VariableOccurrenceTriple → Cell
  | .first => (4, 4)
  | .second => (12, 4)
  | .auxiliary => (20, 4)

/-- Element positions in the outer-face embedding.  The fixed connector
color is the lower leaf of the first triple; the other two connector colors
are the upper and lower leaves of the auxiliary triple. -/
def boundaryElementPosition
    (_variant : VariableOccurrenceVariant) :
    VariableOccurrenceElement → Cell
  | .leftContinuation => (4, 0)
  | .rightContinuation => (12, 0)
  | .cycleShared => (8, 4)
  | .auxiliaryShared => (16, 4)
  | .connectorRed => (20, 0)
  | .connectorGreen =>
      (20, 8)
  | .connectorBlue =>
      (4, 8)

/-- Every incidence of the path-shaped embedding is a direct segment. -/
def boundaryRoute (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple)
    (color : WireColor) : List Cell :=
  directRoute (boundaryTriplePosition triple)
    (boundaryElementPosition variant (reference variant triple color))

/-- Outer-face local drawing with all five degree-one ports exposed. -/
def boundaryDrawing (variant : VariableOccurrenceVariant) :
    LocalIncidenceDrawing
      VariableOccurrenceTriple VariableOccurrenceElement where
  triplePosition := boundaryTriplePosition
  elementPosition := boundaryElementPosition variant
  reference := reference variant
  route := boundaryRoute variant

/-- Both outer-face ordinary templates are valid. -/
theorem boundaryDrawing_isValid
    (variant : VariableOccurrenceVariant) :
    (boundaryDrawing variant).IsValid := by
  cases variant <;> native_decide

/-! The fixed-green connector uses the same logical occurrence tree as the
fixed-blue module, but its three semantic colors occupy a different cyclic
order in the surrounding ribbon.  The following positive-orientation
embedding exposes those connector leaves directly in fixed-green lane order
while retaining the standard two continuation ports. -/

/-- Triple positions in the lane-aligned positive fixed-green embedding. -/
def positiveFixedGreenTriplePosition : VariableOccurrenceTriple → Cell
  | .first => (2, 4)
  | .second => (8, 4)
  | .auxiliary => (6, 10)

/-- Element positions in the lane-aligned positive fixed-green embedding. -/
def positiveFixedGreenElementPosition : VariableOccurrenceElement → Cell
  | .leftContinuation => (4, 0)
  | .rightContinuation => (12, 0)
  | .cycleShared => (5, 4)
  | .auxiliaryShared => (8, 8)
  | .connectorRed => (4, 12)
  | .connectorGreen => (8, 12)
  | .connectorBlue => (0, 12)

/-- Pairwise separated orthogonal incidences of the lane-aligned positive
fixed-green embedding. -/
def positiveFixedGreenRoute
    (triple : VariableOccurrenceTriple)
    (color : WireColor) : List Cell :=
  match triple, color with
  | .first, .red => [(2, 4), (2, 0), (4, 0)]
  | .first, .green => [(2, 4), (5, 4)]
  | .first, .blue => [(2, 4), (0, 4), (0, 12)]
  | .second, .red => [(8, 4), (12, 4), (12, 0)]
  | .second, .green => [(8, 4), (5, 4)]
  | .second, .blue => [(8, 4), (8, 8)]
  | .auxiliary, .red => [(6, 10), (4, 10), (4, 12)]
  | .auxiliary, .green => [(6, 10), (8, 10), (8, 12)]
  | .auxiliary, .blue => [(6, 10), (6, 8), (8, 8)]

/-- Positive fixed-green drawing with its connector leaves ordered as blue,
red, green along the outer boundary. -/
def positiveFixedGreenBoundaryDrawing :
    LocalIncidenceDrawing
      VariableOccurrenceTriple VariableOccurrenceElement where
  triplePosition := positiveFixedGreenTriplePosition
  elementPosition := positiveFixedGreenElementPosition
  reference := reference .fixedGreen
  route := positiveFixedGreenRoute

/-- The lane-aligned fixed-green embedding is a valid local drawing. -/
theorem positiveFixedGreenBoundaryDrawing_isValid :
    positiveFixedGreenBoundaryDrawing.IsValid := by
  native_decide

/-- Reflect a negative occurrence so the continuation for the current slot
is always the left boundary port. -/
def orientedBoundaryDrawing
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    LocalIncidenceDrawing
      VariableOccurrenceTriple VariableOccurrenceElement :=
  match variant, polarity with
  | .fixedGreen, true => positiveFixedGreenBoundaryDrawing
  | variant, true => boundaryDrawing variant
  | variant, false =>
      (boundaryDrawing variant).mapPoints (reflectAcrossVertical 8)

@[simp]
theorem orientedBoundaryDrawing_reference
    (variant : VariableOccurrenceVariant) (polarity : Bool)
    (triple : VariableOccurrenceTriple) (color : WireColor) :
    (orientedBoundaryDrawing variant polarity).reference triple color =
      reference variant triple color := by
  cases variant <;> cases polarity <;> rfl

@[simp]
theorem orientedBoundaryDrawing_slotContinuationPosition
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedBoundaryDrawing variant polarity).elementPosition
        (reference variant
          (slotContinuationTriple polarity) .red) =
      (4, 0) := by
  cases variant <;> cases polarity <;> native_decide

@[simp]
theorem orientedBoundaryDrawing_nextContinuationPosition
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedBoundaryDrawing variant polarity).elementPosition
        (reference variant
          (nextContinuationTriple polarity) .red) =
      (12, 0) := by
  cases variant <;> cases polarity <;> native_decide

/-- The standardized outer-face ordinary template remains valid for either
polarity. -/
theorem orientedBoundaryDrawing_isValid
    (variant : VariableOccurrenceVariant) (polarity : Bool) :
    (orientedBoundaryDrawing variant polarity).IsValid := by
  cases variant <;> cases polarity <;> native_decide

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

/-- Reflect positive fixed-red occurrences so that the continuation incident
to the current slot is always the upper of the two left boundary ports. -/
def orientedDrawing (polarity : Bool) :
    LocalIncidenceDrawing
      FixedRedConnectorTriple FixedRedConnectorElement :=
  if polarity then
    drawing.mapPoints (reflectAcrossHorizontal 2)
  else
    drawing

@[simp]
theorem orientedDrawing_reference
    (polarity : Bool) (triple : FixedRedConnectorTriple)
    (color : WireColor) :
    (orientedDrawing polarity).reference triple color =
      reference triple color := by
  cases polarity <;> rfl

/-- Fixed-red triple incident to the current occurrence slot. -/
def slotContinuationTriple
    (polarity : Bool) : FixedRedConnectorTriple :=
  if polarity then .bottomLeft else .topLeft

/-- Fixed-red triple incident to the next used occurrence slot. -/
def nextContinuationTriple
    (polarity : Bool) : FixedRedConnectorTriple :=
  if polarity then .topLeft else .bottomLeft

/-- The current-slot fixed-red continuation always occupies the upper
boundary point. -/
@[simp]
theorem orientedDrawing_slotContinuationPosition
    (polarity : Bool) :
    (orientedDrawing polarity).elementPosition
        (reference
          (slotContinuationTriple polarity) .red) =
      (-2, 0) := by
  cases polarity <;> native_decide

/-- The next-slot fixed-red continuation always occupies the lower boundary
point. -/
@[simp]
theorem orientedDrawing_nextContinuationPosition
    (polarity : Bool) :
    (orientedDrawing polarity).elementPosition
        (reference
          (nextContinuationTriple polarity) .red) =
      (-2, 4) := by
  cases polarity <;> native_decide

/-- The polarity-normalized fixed-red template remains a certified planar
orthogonal drawing. -/
theorem orientedDrawing_isValid (polarity : Bool) :
    (orientedDrawing polarity).IsValid := by
  cases polarity <;> native_decide

/-! ## Standardized outer-face boundary template -/

/-- Stretch and translate the rotated fixed-red module so its two cycle
ports agree with the ordinary template's standard points. -/
def normalizeFixedRedBoundary (point : Cell) : Cell :=
  (2 * point.1 + 4, point.2 - 2)

/-- Rotate the fixed-red module, reflect positive polarity to put the current
slot first, normalize the continuation spacing, and place the module above
the common cycle-port line. -/
def boundaryDrawing (polarity : Bool) :
    LocalIncidenceDrawing
      FixedRedConnectorTriple FixedRedConnectorElement :=
  let rotated := drawing.mapPoints rotateClockwise
  let oriented :=
    if polarity then
      rotated.mapPoints (reflectAcrossVertical 2)
    else
      rotated
  (oriented.mapPoints normalizeFixedRedBoundary).mapPoints
    (reflectAcrossHorizontal 0)

@[simp]
theorem boundaryDrawing_reference
    (polarity : Bool) (triple : FixedRedConnectorTriple)
    (color : WireColor) :
    (boundaryDrawing polarity).reference triple color =
      reference triple color := by
  cases polarity <;> rfl

@[simp]
theorem boundaryDrawing_slotContinuationPosition
    (polarity : Bool) :
    (boundaryDrawing polarity).elementPosition
        (reference
          (slotContinuationTriple polarity) .red) =
      (4, 0) := by
  cases polarity <;> native_decide

@[simp]
theorem boundaryDrawing_nextContinuationPosition
    (polarity : Bool) :
    (boundaryDrawing polarity).elementPosition
        (reference
          (nextContinuationTriple polarity) .red) =
      (12, 0) := by
  cases polarity <;> native_decide

/-- The standardized fixed-red boundary template is valid for either
polarity. -/
theorem boundaryDrawing_isValid (polarity : Bool) :
    (boundaryDrawing polarity).IsValid := by
  cases polarity <;> native_decide

end FixedRedConnector

end PlanarThreeDM
end LeanTrominoes
