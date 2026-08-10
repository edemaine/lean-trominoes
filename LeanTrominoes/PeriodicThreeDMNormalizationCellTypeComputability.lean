import LeanTrominoes.PeriodicThreeDMNormalizationRoute3Computability

/-!
# Primitive-recursive normalized cell classification

This module computes routing-cell shapes, final vertex-cell types, and the
final square period before torus rasterization.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

abbrev RoutingCellInput :=
  (Cell × Cell × Cell) × WireColor

def routingCellTypeFromDirections
    (input : (AxisDirection × AxisDirection) × WireColor) :
    OrthogonalCellType :=
  routingCellType
    (Side.ofAxisDirection input.1.1)
    (Side.ofAxisDirection input.1.2)
    input.2

theorem routingCellTypeFromDirections_primrec :
    Primrec routingCellTypeFromDirections :=
  Primrec.dom_finite _

theorem routingCellTypeAt_primrec :
    Primrec fun input : RoutingCellInput =>
      routingCellTypeAt input.1.1 input.1.2.1 input.1.2.2 input.2 := by
  have incoming : Primrec (fun input : RoutingCellInput =>
      AxisDirection.between input.1.2.1 input.1.1) :=
    axisDirection_between_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.fst)
  have outgoing : Primrec (fun input : RoutingCellInput =>
      AxisDirection.between input.1.2.1 input.1.2.2) :=
    axisDirection_between_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (routingCellTypeFromDirections_primrec.comp
    (Primrec.pair (Primrec.pair incoming outgoing) Primrec.snd)).of_eq
      fun _ => rfl

abbrev VertexCellKind := WireColor ⊕ Unit

def vertexCellKind : PeriodicThreeDMVertex → VertexCellKind
  | .triple _ => .inr ()
  | .element color _ => .inl color

theorem vertexCellKind_primrec : Primrec vertexCellKind := by
  exact (Primrec.sumCasesOn PeriodicThreeDMVertex.equivData_primrec
    (Primrec.sumInr.comp (Primrec.const ())).to₂
    (Primrec.sumInl.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq
      fun vertex => by cases vertex <;> rfl

def trichromaticOrderFromData
    (data : Option EndpointTripleData) : TrichromaticOrder :=
  trichromaticOrder fun port => canonicalColorFromData (data, port)

theorem trichromaticOrderFromData_primrec :
    Primrec trichromaticOrderFromData :=
  Primrec.dom_finite _

theorem trichromaticOrderFromData_at
    (input : Input × PeriodicThreeDMVertex) :
    trichromaticOrderFromData (endpointTripleDataAt input) =
      trichromaticOrder (canonicalColoringAt input.1 input.2) := by
  apply congrArg trichromaticOrder
  funext port
  exact canonicalColorFromData_endpointTripleDataAt input port

def finalVertexCellTypeFromData
    (input : VertexCellKind × Option EndpointTripleData) :
    OrthogonalCellType :=
  match input.1 with
  | .inl color => .monochromaticVertex color
  | .inr _ => .trichromaticVertex (trichromaticOrderFromData input.2)

theorem finalVertexCellTypeFromData_primrec :
    Primrec finalVertexCellTypeFromData :=
  Primrec.dom_finite _

theorem finalVertexCellType_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      finalVertexCellType input.1 input.2 := by
  have kind : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      vertexCellKind input.2) :=
    vertexCellKind_primrec.comp Primrec.snd
  have data : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      endpointTripleDataAt input) :=
    endpointTripleDataAt_primrec
  exact (finalVertexCellTypeFromData_primrec.comp
    (Primrec.pair kind data)).of_eq fun input => by
      rcases input with ⟨compilerInput, vertex⟩
      cases vertex with
      | element color atom => rfl
      | triple index =>
          unfold finalVertexCellTypeFromData vertexCellKind
            finalVertexCellType
          exact congrArg OrthogonalCellType.trichromaticVertex
            (trichromaticOrderFromData_at
              (compilerInput, .triple index))

theorem finalNormalizationPeriod_primrec :
    Primrec finalNormalizationPeriod := by
  have gridSize : Primrec fun input : Input =>
      (contractedDrawing input).gridSize :=
    PeriodicGridDrawing.gridSize_primrec.comp contractedDrawing_primrec
  exact (Primrec.nat_mul.comp
    (Primrec.const (vertexNormalizationScaleNat ^ 3)) gridSize).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
