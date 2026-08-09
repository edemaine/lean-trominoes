import LeanTrominoes.PeriodicThreeDMContractedVertexFans

/-!
# Executable route data for degree-three vertex normalization

This module defines the geometric data of the three finite replacement
rounds used by Lemma 2.3.  The first round replaces each arbitrary
three-direction fan by canonical west/north/east ports.  Two subsequent
rounds apply either the identity template or the clockwise cyclic template,
so every trichromatic vertex ends with red at its north port.

Each round magnifies coordinates by twelve.  The `6 × 6` local template then
occupies a radius-three neighborhood of the magnified old vertex, leaving a
six-cell corridor even between formerly adjacent lattice points.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Linear magnification used between successive local replacements. -/
def vertexNormalizationScale : Int := 12

/-- New vertex center corresponding to an old lattice position. -/
def normalizeVertexPosition (position : Cell) : Cell :=
  Cell.add (Cell.scale vertexNormalizationScale position) center

/-- Anchor a `6 × 6` template at the magnified old position. -/
def normalizationTemplateAt (position : Cell) (points : List Cell) :
    List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (Cell.scale vertexNormalizationScale position) points

/-- Magnify an old route and subdivide it into unit steps. -/
def magnifiedUnitRoute (points : List Cell) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (points.map normalizeVertexPosition)

/-- Remove the three unit steps lying in each endpoint's replacement
neighborhood.  The remaining list includes both boundary points. -/
def trimmedMagnifiedRoute (points : List Cell) : List Cell :=
  let magnified := magnifiedUnitRoute points
  (magnified.drop 3).take (magnified.length - 6)

/-- Splice two outward local templates onto the trimmed magnified old
route.  The target template is traversed in reverse. -/
def normalizeRouteWithTemplates
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell) : List Cell :=
  joinAtEndpoint
    (normalizationTemplateAt sourcePosition sourceTemplate)
    (joinAtEndpoint
      (trimmedMagnifiedRoute oldRoute)
      (normalizationTemplateAt targetPosition targetTemplate).reverse)

/-- The three endpoints at a vertex, when the executable list has the
promised shape. -/
def endpointTripleAt (problem : PeriodicThreeDM)
    (vertex : PeriodicThreeDMVertex) :
    Option (ContractedEndpoint × ContractedEndpoint × ContractedEndpoint) :=
  match problem.contractedEndpointsAt vertex with
  | [first, second, third] => some (first, second, third)
  | _ => none

/-- Data-only omitted-side selection, with an irrelevant east fallback for
malformed inputs. -/
def omittedSideAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : VertexSide :=
  match problem.endpointTripleAt vertex with
  | some (first, second, third) =>
      omittedSide
        (first.outwardSide presentation)
        (second.outwardSide presentation)
        (third.outwardSide presentation)
  | none => .east

/-- Color found on one old side of the executable fan. -/
def endpointColorAtSide
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex)
    (side : VertexSide) : WireColor :=
  match problem.endpointTripleAt vertex with
  | some (first, second, third) =>
      if side = first.outwardSide presentation then first.color
      else if side = second.outwardSide presentation then second.color
      else third.color
  | none => .red

/-- Port coloring after the first, direction-normalizing replacement. -/
def canonicalColoringAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) :
    CanonicalVertexPort → WireColor :=
  fun port => endpointColorAtSide presentation vertex
    (boundarySide (omittedSideAt presentation vertex) port)

/-- Number of clockwise replacement rounds selected for one vertex.
Monochromatic vertices need no rotation. -/
def rotationCountAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicThreeDMVertex → PortRotationCount
  | vertex@(.triple _) =>
      rotationsToNorth
        (portOfColor (canonicalColoringAt presentation vertex) .red)
  | .element _ _ => PortRotationCount.zero

/-- Canonical port occupied by an endpoint after the first replacement. -/
def ContractedEndpoint.firstNormalizedPort
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  canonicalPortForSide
    (omittedSideAt presentation endpoint.vertex)
    (endpoint.outwardSide presentation)

/-- Inverse of the clockwise template's new-port-to-old-port map. -/
def newPortAfterClockwise : CanonicalVertexPort → CanonicalVertexPort
  | .west => .north
  | .north => .east
  | .east => .west

@[simp]
theorem oldPortAfterClockwise_newPortAfterClockwise
    (port : CanonicalVertexPort) :
    oldPortAfterClockwise (newPortAfterClockwise port) = port := by
  cases port <;> rfl

/-- Whether the first cyclic-rotation round is active at this vertex. -/
def firstRotationActive
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Bool :=
  rotationCountAt presentation vertex != PortRotationCount.zero

/-- Whether the second cyclic-rotation round is active at this vertex. -/
def secondRotationActive
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Bool :=
  rotationCountAt presentation vertex == PortRotationCount.two

/-- New port and local route for one old canonical port in a selected
rotation round. -/
def rotationRoundPortAndRoute (active : Bool)
    (oldPort : CanonicalVertexPort) :
    CanonicalVertexPort × List Cell :=
  if active then
    let newPort := newPortAfterClockwise oldPort
    (newPort, clockwiseRotationRoute newPort)
  else
    (oldPort, identityRotationRoute oldPort)

/-- Endpoint port after the first cyclic-rotation round. -/
def ContractedEndpoint.secondNormalizedPort
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  (rotationRoundPortAndRoute
    (firstRotationActive presentation endpoint.vertex)
    (endpoint.firstNormalizedPort presentation)).1

/-- Endpoint port after the second cyclic-rotation round. -/
def ContractedEndpoint.finalNormalizedPort
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  (rotationRoundPortAndRoute
    (secondRotationActive presentation endpoint.vertex)
    (endpoint.secondNormalizedPort presentation)).1

/-- Local Figure 2 route used at an endpoint in the first replacement. -/
def ContractedEndpoint.firstNormalizationTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : List Cell :=
  route (omittedSideAt presentation endpoint.vertex)
    (endpoint.firstNormalizedPort presentation)

/-- Local route used at an endpoint in the first cyclic round. -/
def ContractedEndpoint.secondNormalizationTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : List Cell :=
  (rotationRoundPortAndRoute
    (firstRotationActive presentation endpoint.vertex)
    (endpoint.firstNormalizedPort presentation)).2

/-- Local route used at an endpoint in the second cyclic round. -/
def ContractedEndpoint.finalNormalizationTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : List Cell :=
  (rotationRoundPortAndRoute
    (secondRotationActive presentation endpoint.vertex)
    (endpoint.secondNormalizedPort presentation)).2

/-- Prototype vertex position after zero, one, two, or all three
replacement rounds. -/
def PlanarPresentation.normalizationPosition0
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  presentation.contractedDrawing.vertexPosition problem.contractedGraph vertex

def PlanarPresentation.normalizationPosition1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (presentation.normalizationPosition0 vertex)

def PlanarPresentation.normalizationPosition2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (presentation.normalizationPosition1 vertex)

def PlanarPresentation.finalNormalizationPosition
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (presentation.normalizationPosition2 vertex)

/-- The stored target occurrence, including its periodic edge offset, at
each geometric stage. -/
def PlanarPresentation.normalizationTarget0
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : Cell :=
  Cell.add
    (presentation.normalizationPosition0 edge.toPeriodicEdge.target)
    (presentation.contractedDrawing.periodTranslation
      edge.toPeriodicEdge.offset)

def PlanarPresentation.normalizationTarget1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : Cell :=
  normalizeVertexPosition (presentation.normalizationTarget0 edge)

def PlanarPresentation.normalizationTarget2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : Cell :=
  normalizeVertexPosition (presentation.normalizationTarget1 edge)

/-- Edge route after direction normalization. -/
def PlanarPresentation.normalizationRoute1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (presentation.normalizationPosition0 edge.toPeriodicEdge.source)
    (presentation.normalizationTarget0 edge)
    ((ContractedEndpoint.source edge).firstNormalizationTemplate presentation)
    ((ContractedEndpoint.target edge).firstNormalizationTemplate presentation)
    (presentation.contractedEdgeRoute edge)

/-- Edge route after the first cyclic-rotation round. -/
def PlanarPresentation.normalizationRoute2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (presentation.normalizationPosition1 edge.toPeriodicEdge.source)
    (presentation.normalizationTarget1 edge)
    ((ContractedEndpoint.source edge).secondNormalizationTemplate presentation)
    ((ContractedEndpoint.target edge).secondNormalizationTemplate presentation)
    (presentation.normalizationRoute1 edge)

/-- Final edge route after both cyclic-rotation rounds. -/
def PlanarPresentation.finalNormalizationRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
    (presentation.normalizationTarget2 edge)
    ((ContractedEndpoint.source edge).finalNormalizationTemplate presentation)
    ((ContractedEndpoint.target edge).finalNormalizationTemplate presentation)
    (presentation.normalizationRoute2 edge)

/-- Cell type placed at the final normalized occurrence of a contracted
vertex. -/
def PlanarPresentation.finalVertexCellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicThreeDMVertex → OrthogonalCellType
  | .triple tripleIndex =>
      .trichromaticVertex
        (trichromaticOrder
          (canonicalColoringAt presentation (.triple tripleIndex)))
  | .element color _ => .monochromaticVertex color

end PeriodicThreeDM
end LeanTrominoes
