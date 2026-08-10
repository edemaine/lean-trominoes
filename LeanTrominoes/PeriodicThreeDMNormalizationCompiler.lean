import LeanTrominoes.PeriodicThreeDMNormalizationEncoding

/-!
# Data-only compiler for normalized periodic 3DM drawings

`PlanarPresentation` carries geometric correctness proofs, but none of those
proofs is inspected while rasterizing.  This module factors the executable
part of normalization through an explicit pair of finite data: the periodic
3DM problem and its periodic grid drawing.  The final theorem identifies this
compiler definitionally with the previously verified presentation-level
construction.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Exactly the finite runtime input used by normalization. -/
structure Input where
  problem : PeriodicThreeDM
  drawing : PeriodicGridDrawing
  deriving DecidableEq, Repr

namespace Input

/-- Product representation of the compiler input. -/
def equivData : Input ≃ PeriodicThreeDM × PeriodicGridDrawing where
  toFun input := (input.problem, input.drawing)
  invFun data := ⟨data.1, data.2⟩
  left_inv input := by cases input; rfl
  right_inv data := by rcases data with ⟨problem, drawing⟩; rfl

noncomputable instance : Primcodable Input :=
  Primcodable.ofEquiv (PeriodicThreeDM × PeriodicGridDrawing) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem problem_primrec : Primrec Input.problem :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem drawing_primrec : Primrec Input.drawing :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

end Input

/-- Original incidence route selected by its stable colored tag. -/
def incidenceRoute (input : Input) (tag : IncidenceTag) : List Cell :=
  input.drawing.edgeRoute (input.problem.incidenceRouteIndex tag)

/-- Translate and reverse the target incidence route of a suppressed edge. -/
def reversedIncidenceRouteAt (input : Input)
    (color : WireColor) (first second : Incidence) : List Cell :=
  (translatePolyline
    (input.drawing.periodTranslation
      (Cell.sub first.offset second.offset))
    (incidenceRoute input ⟨second.tripleIndex, color⟩)).reverse

/-- Retained route or concatenated route through a suppressed element. -/
def contractedEdgeRoute (input : Input) : ContractedEdge → List Cell
  | .retained color _atom incidence =>
      incidenceRoute input ⟨incidence.tripleIndex, color⟩
  | .through color _atom first second =>
      joinPolylines
        (incidenceRoute input ⟨first.tripleIndex, color⟩)
        (reversedIncidenceRouteAt input color first second)

/-- Original positions restricted to vertices retained by contraction. -/
def contractedVertexPositions (input : Input) : List Cell :=
  input.problem.contractedGraph.vertices.zipIdx.map fun tagged =>
    input.drawing.vertexPosition input.problem.incidenceGraph tagged.1

/-- Complete data-only contracted drawing. -/
def contractedDrawing (input : Input) : PeriodicGridDrawing where
  gridSizePred := input.drawing.gridSizePred
  vertexPositions := contractedVertexPositions input
  edgeRoutes := input.problem.contractedEdges.zipIdx.map fun tagged =>
    contractedEdgeRoute input tagged.1

/-- Direction pointing from an endpoint into its contracted route. -/
def outwardDirection (input : Input) : ContractedEndpoint → AxisDirection
  | .source edge =>
      AxisDirection.polylineFirstDirection (contractedEdgeRoute input edge)
  | .target edge =>
      (AxisDirection.polylineLastDirection
        (contractedEdgeRoute input edge)).opposite

/-- Cardinal template side corresponding to an endpoint direction. -/
def outwardSide (input : Input) (endpoint : ContractedEndpoint) : VertexSide :=
  VertexSide.ofDirection (outwardDirection input endpoint)

/-- Data-only omitted-side selection at a contracted vertex. -/
def omittedSideAt (input : Input) (vertex : PeriodicThreeDMVertex) :
    VertexSide :=
  match input.problem.endpointTripleAt vertex with
  | some (first, second, third) =>
      omittedSide (outwardSide input first)
        (outwardSide input second) (outwardSide input third)
  | none => .east

/-- Color found on one old side of an executable contracted fan. -/
def endpointColorAtSide (input : Input) (vertex : PeriodicThreeDMVertex)
    (side : VertexSide) : WireColor :=
  match input.problem.endpointTripleAt vertex with
  | some (first, second, third) =>
      if side = outwardSide input first then first.color
      else if side = outwardSide input second then second.color
      else third.color
  | none => .red

/-- Port coloring after direction normalization. -/
def canonicalColoringAt (input : Input) (vertex : PeriodicThreeDMVertex) :
    CanonicalVertexPort → WireColor :=
  fun port => endpointColorAtSide input vertex
    (boundarySide (omittedSideAt input vertex) port)

/-- Number of clockwise cyclic replacements selected for a vertex. -/
def rotationCountAt (input : Input) :
    PeriodicThreeDMVertex → PortRotationCount
  | vertex@(.triple _) =>
      rotationsToNorth (portOfColor (canonicalColoringAt input vertex) .red)
  | .element _ _ => .zero

/-- Canonical port occupied after the first replacement. -/
def firstNormalizedPort (input : Input)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  canonicalPortForSide
    (omittedSideAt input endpoint.vertex)
    (outwardSide input endpoint)

/-- Whether the first cyclic rotation is active at a vertex. -/
def firstRotationActive (input : Input)
    (vertex : PeriodicThreeDMVertex) : Bool :=
  rotationCountAt input vertex != .zero

/-- Whether the second cyclic rotation is active at a vertex. -/
def secondRotationActive (input : Input)
    (vertex : PeriodicThreeDMVertex) : Bool :=
  rotationCountAt input vertex == .two

/-- Endpoint port after the first cyclic round. -/
def secondNormalizedPort (input : Input)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  (rotationRoundPortAndRoute
    (firstRotationActive input endpoint.vertex)
    (firstNormalizedPort input endpoint)).1

/-- Endpoint port after the second cyclic round. -/
def finalNormalizedPort (input : Input)
    (endpoint : ContractedEndpoint) : CanonicalVertexPort :=
  (rotationRoundPortAndRoute
    (secondRotationActive input endpoint.vertex)
    (secondNormalizedPort input endpoint)).1

/-- Local first-round endpoint template. -/
def firstNormalizationTemplate (input : Input)
    (endpoint : ContractedEndpoint) : List Cell :=
  route (omittedSideAt input endpoint.vertex)
    (firstNormalizedPort input endpoint)

/-- Local first cyclic-round endpoint template. -/
def secondNormalizationTemplate (input : Input)
    (endpoint : ContractedEndpoint) : List Cell :=
  (rotationRoundPortAndRoute
    (firstRotationActive input endpoint.vertex)
    (firstNormalizedPort input endpoint)).2

/-- Local second cyclic-round endpoint template. -/
def finalNormalizationTemplate (input : Input)
    (endpoint : ContractedEndpoint) : List Cell :=
  (rotationRoundPortAndRoute
    (secondRotationActive input endpoint.vertex)
    (secondNormalizedPort input endpoint)).2

/-- Prototype vertex position before the three affine replacements. -/
def normalizationPosition0 (input : Input)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  (contractedDrawing input).vertexPosition input.problem.contractedGraph vertex

/-- Prototype vertex position after the first affine replacement. -/
def normalizationPosition1 (input : Input)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (normalizationPosition0 input vertex)

/-- Prototype vertex position after the second affine replacement. -/
def normalizationPosition2 (input : Input)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (normalizationPosition1 input vertex)

/-- Final normalized prototype vertex position. -/
def finalNormalizationPosition (input : Input)
    (vertex : PeriodicThreeDMVertex) : Cell :=
  normalizeVertexPosition (normalizationPosition2 input vertex)

/-- Target occurrence before the three affine replacements. -/
def normalizationTarget0 (input : Input) (edge : ContractedEdge) : Cell :=
  Cell.add
    (normalizationPosition0 input edge.toPeriodicEdge.target)
    ((contractedDrawing input).periodTranslation edge.toPeriodicEdge.offset)

/-- Target occurrence after the first affine replacement. -/
def normalizationTarget1 (input : Input) (edge : ContractedEdge) : Cell :=
  normalizeVertexPosition (normalizationTarget0 input edge)

/-- Target occurrence after the second affine replacement. -/
def normalizationTarget2 (input : Input) (edge : ContractedEdge) : Cell :=
  normalizeVertexPosition (normalizationTarget1 input edge)

/-- Edge route after direction normalization. -/
def normalizationRoute1 (input : Input) (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (normalizationPosition0 input edge.toPeriodicEdge.source)
    (normalizationTarget0 input edge)
    (firstNormalizationTemplate input (.source edge))
    (firstNormalizationTemplate input (.target edge))
    (contractedEdgeRoute input edge)

/-- Edge route after the first cyclic-rotation round. -/
def normalizationRoute2 (input : Input) (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (normalizationPosition1 input edge.toPeriodicEdge.source)
    (normalizationTarget1 input edge)
    (secondNormalizationTemplate input (.source edge))
    (secondNormalizationTemplate input (.target edge))
    (normalizationRoute1 input edge)

/-- Edge route after all three normalization rounds. -/
def finalNormalizationRoute (input : Input) (edge : ContractedEdge) : List Cell :=
  normalizeRouteWithTemplates
    (normalizationPosition2 input edge.toPeriodicEdge.source)
    (normalizationTarget2 input edge)
    (finalNormalizationTemplate input (.source edge))
    (finalNormalizationTemplate input (.target edge))
    (normalizationRoute2 input edge)

/-- Cell type placed at a final contracted vertex. -/
def finalVertexCellType (input : Input) :
    PeriodicThreeDMVertex → OrthogonalCellType
  | .triple tripleIndex =>
      .trichromaticVertex
        (trichromaticOrder
          (canonicalColoringAt input (.triple tripleIndex)))
  | .element color _ => .monochromaticVertex color

/-- Positive square period after all three rounds. -/
def finalNormalizationPeriod (input : Input) : Nat :=
  vertexNormalizationScaleNat ^ 3 * (contractedDrawing input).gridSize

/-- Vertex assignments, with priority over route interiors. -/
def finalVertexAssignments (input : Input) :
    List NormalizedCellAssignment :=
  input.problem.contractedGraph.vertices.map fun vertex =>
    (rasterLocation (finalNormalizationPeriod input)
      (finalNormalizationPosition input vertex),
      finalVertexCellType input vertex)

/-- Routing assignments in contracted-edge order. -/
def finalRouteAssignments (input : Input) :
    List NormalizedCellAssignment :=
  input.problem.contractedEdges.flatMap fun edge =>
    routeInteriorAssignments (finalNormalizationPeriod input)
      edge.color (finalNormalizationRoute input edge)

/-- Complete prioritized assignment list. -/
def finalCellAssignments (input : Input) :
    List NormalizedCellAssignment :=
  finalVertexAssignments input ++ finalRouteAssignments input

/-- Total cell lookup with a blank fallback. -/
def finalCellTypeAt (input : Input) (location : Cell) : OrthogonalCellType :=
  ((finalCellAssignments input).lookup location).getD .blank

/-- Row-major finite torus array. -/
def finalCellTypes (input : Input) : List OrthogonalCellType :=
  rowMajorList (finalNormalizationPeriod input)
    (finalNormalizationPeriod input) fun horizontal vertical =>
      finalCellTypeAt input (horizontal, vertical)

/-- The complete data-only normalized orthogonal drawing compiler. -/
def compile (input : Input) : PeriodicOrthogonalDrawing where
  horizontalPeriodPred := finalNormalizationPeriod input - 1
  verticalPeriodPred := finalNormalizationPeriod input - 1
  cellTypes := finalCellTypes input

/-- Forget a presentation's certificates and retain exactly its runtime data. -/
def inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : Input :=
  ⟨problem, presentation.drawing⟩

/-- The data-only compiler is definitionally the verified presentation-level
normalization. -/
theorem compile_inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    compile (inputOfPresentation presentation) =
      presentation.normalizedOrthogonalDrawing := by
  set_option maxRecDepth 100000 in
    rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
