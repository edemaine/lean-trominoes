import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

/-!
# Computability of normalized periodic 3DM routes

This file continues the primitive-recursive normalized-drawing compiler at
the route-normalization layer.  Its first step computes the local three-edge
fan and the unused side at each retained vertex.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem outwardDirection_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      outwardDirection input.1 input.2 := by
  let Combined := Input × ContractedEndpoint
  have route : Primrec (fun input : Combined =>
      contractedEdgeRoute input.1 input.2.edge) :=
    contractedEdgeRoute_primrec.comp
      Primrec.fst
      (contractedEndpoint_edge_primrec.comp Primrec.snd)
  have source : PrimrecPred fun input : Combined =>
      input.2.isSource = true := by
    exact Primrec.eq.comp
      (contractedEndpoint_isSource_primrec.comp Primrec.snd)
      (Primrec.const true)
  exact (Primrec.ite source
    (polylineFirstDirection_primrec.comp route)
    (axisDirection_opposite_primrec.comp
      (polylineLastDirection_primrec.comp route))).of_eq fun input => by
        cases input.2 <;> rfl

theorem outwardSide_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      outwardSide input.1 input.2 :=
  vertexSide_ofDirection_primrec.comp outwardDirection_primrec

theorem vertexSideCode_primrec :
    Primrec fun side : VertexSide =>
      match side with
      | .east => 0 | .north => 1 | .west => 2 | .south => 3 :=
  Primrec.dom_finite _

theorem omittedSide_primrec :
    Primrec fun input : VertexSide × VertexSide × VertexSide =>
      omittedSide input.1 input.2.1 input.2.2 :=
  Primrec.dom_finite _

theorem omittedSideAt_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      omittedSideAt input.1 input.2 := by
  let Combined := Input × PeriodicThreeDMVertex
  have problemAndVertex : Primrec (fun input : Combined =>
      (input.1.problem, input.2)) :=
    Primrec.pair
      (Input.problem_primrec.comp Primrec.fst) Primrec.snd
  have triple : Primrec (fun input : Combined =>
      input.1.problem.endpointTripleAt input.2) := by
    exact (endpointTripleAt_primrec.comp problemAndVertex).of_eq
      fun _ => rfl
  have selected : Primrec₂ fun (input : Combined)
      (endpoints : ContractedEndpoint × ContractedEndpoint ×
        ContractedEndpoint) =>
      omittedSide
        (outwardSide input.1 endpoints.1)
        (outwardSide input.1 endpoints.2.1)
        (outwardSide input.1 endpoints.2.2) := by
    exact (omittedSide_primrec.comp
      (Primrec.pair
        (outwardSide_primrec.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp Primrec.snd)))
        (Primrec.pair
          (outwardSide_primrec.comp
            (Primrec.pair
              (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
          (outwardSide_primrec.comp
            (Primrec.pair
              (Primrec.fst.comp Primrec.fst)
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))).to₂
  exact (Primrec.option_casesOn triple (Primrec.const .east)
    selected).of_eq fun input => by
      unfold omittedSideAt
      cases input.1.problem.endpointTripleAt input.2 <;> rfl

/-! ## Finite template control -/

theorem boundarySide_primrec :
    Primrec fun input : VertexSide × CanonicalVertexPort =>
      boundarySide input.1 input.2 :=
  Primrec.dom_finite _

theorem canonicalPortForSide_primrec :
    Primrec fun input : VertexSide × VertexSide =>
      canonicalPortForSide input.1 input.2 :=
  Primrec.dom_finite _

theorem rotationsToNorth_primrec :
    Primrec rotationsToNorth :=
  Primrec.dom_finite _

theorem normalizationTemplateRoute_primrec :
    Primrec fun input : VertexSide × CanonicalVertexPort =>
      route input.1 input.2 :=
  Primrec.dom_finite _

theorem rotationRoundPortAndRoute_primrec :
    Primrec fun input : Bool × CanonicalVertexPort =>
      rotationRoundPortAndRoute input.1 input.2 :=
  Primrec.dom_finite _

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
