/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointPortComputability

/-! # Finite endpoint data for route-request headers -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open DegreeThreeVertexNormalization
open NormalizationCompiler

/-- All information needed to select the three finite normalization choices
at one endpoint.  Geometry has already been compressed to finite sides and
colors. -/
structure EndpointHeaderData where
  vertexIsTriple : Bool
  fan : Option EndpointTripleData
  endpoint : EndpointSideColor
  deriving DecidableEq, Fintype, Repr

/-- The first-round template selected solely from finite endpoint data. -/
def EndpointHeaderData.firstChoice
    (data : EndpointHeaderData) : FirstTemplateChoice :=
  { omitted := omittedSideFromData data.fan
    port := firstPortFromData (data.fan, data.endpoint) }

/-- The number of cyclic rounds selected solely from finite endpoint data. -/
def EndpointHeaderData.rotationCount
    (data : EndpointHeaderData) : PortRotationCount :=
  rotationCountFromData (data.vertexIsTriple, data.fan)

/-- The second-round template selected solely from finite endpoint data. -/
def EndpointHeaderData.secondChoice
    (data : EndpointHeaderData) : RotationTemplateChoice :=
  { active := firstRotationActiveFromCount data.rotationCount
    port := firstPortFromData (data.fan, data.endpoint) }

/-- The endpoint port after the first cyclic round. -/
def EndpointHeaderData.secondPort
    (data : EndpointHeaderData) : CanonicalVertexPort :=
  (rotationRoundPortAndRoute
    (firstRotationActiveFromCount data.rotationCount)
    (firstPortFromData (data.fan, data.endpoint))).1

/-- The final-round template selected solely from finite endpoint data. -/
def EndpointHeaderData.finalChoice
    (data : EndpointHeaderData) : RotationTemplateChoice :=
  { active := secondRotationActiveFromCount data.rotationCount
    port := data.secondPort }

/-- Package the finite normalization data read at one compiler endpoint. -/
def endpointHeaderData (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) : EndpointHeaderData :=
  { vertexIsTriple := NormalizationCompiler.vertexIsTriple endpoint.vertex
    fan := endpointTripleDataAt (input, endpoint.vertex)
    endpoint := endpointSideColor (input, endpoint) }

/-- Build the complete six-field request header from its two finite endpoint
records. -/
def Header.ofEndpointData
    (source target : EndpointHeaderData) : Header :=
  { firstSource := source.firstChoice
    firstTarget := target.firstChoice
    secondSource := source.secondChoice
    secondTarget := target.secondChoice
    finalSource := source.finalChoice
    finalTarget := target.finalChoice }

@[simp] theorem omittedSideFromData_endpointTripleDataAt
    (input : NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    omittedSideFromData (endpointTripleDataAt (input, vertex)) =
      NormalizationCompiler.omittedSideAt input vertex := by
  unfold omittedSideFromData endpointTripleDataAt
    NormalizationCompiler.omittedSideAt
  generalize input.problem.endpointTripleAt vertex = endpoints
  cases endpoints with
  | none => rfl
  | some endpoints =>
      rcases endpoints with ⟨first, second, third⟩
      rfl

@[simp] theorem endpointHeaderData_firstChoice
    (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) :
    (endpointHeaderData input endpoint).firstChoice =
      { omitted := NormalizationCompiler.omittedSideAt
          input endpoint.vertex
        port := NormalizationCompiler.firstNormalizedPort
          input endpoint } := by
  change FirstTemplateChoice.mk _ _ = FirstTemplateChoice.mk _ _
  congr 1
  · exact omittedSideFromData_endpointTripleDataAt
      input endpoint.vertex
  · exact firstPortFromData_endpoint (input, endpoint)

@[simp] theorem endpointHeaderData_rotationCount
    (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) :
    (endpointHeaderData input endpoint).rotationCount =
      NormalizationCompiler.rotationCountAt input endpoint.vertex := by
  exact rotationCountFromData_at (input, endpoint.vertex)

@[simp] theorem endpointHeaderData_secondChoice
    (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) :
    (endpointHeaderData input endpoint).secondChoice =
      { active := NormalizationCompiler.firstRotationActive
          input endpoint.vertex
        port := NormalizationCompiler.firstNormalizedPort
          input endpoint } := by
  change RotationTemplateChoice.mk _ _ = RotationTemplateChoice.mk _ _
  congr 1
  · rw [show (endpointHeaderData input endpoint).rotationCount =
        NormalizationCompiler.rotationCountAt input endpoint.vertex from
      endpointHeaderData_rotationCount input endpoint]
    rfl
  · exact firstPortFromData_endpoint (input, endpoint)

@[simp] theorem endpointHeaderData_secondPort
    (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) :
    (endpointHeaderData input endpoint).secondPort =
      NormalizationCompiler.secondNormalizedPort input endpoint := by
  change
    (rotationRoundPortAndRoute
      (firstRotationActiveFromCount
        (endpointHeaderData input endpoint).rotationCount)
      (firstPortFromData
        (endpointTripleDataAt (input, endpoint.vertex),
          endpointSideColor (input, endpoint)))).1 = _
  rw [endpointHeaderData_rotationCount]
  unfold NormalizationCompiler.secondNormalizedPort
  have activeEq :
      firstRotationActiveFromCount
          (NormalizationCompiler.rotationCountAt input endpoint.vertex) =
        NormalizationCompiler.firstRotationActive
          input endpoint.vertex := by
    rfl
  have portEq :
      firstPortFromData
          (endpointTripleDataAt (input, endpoint.vertex),
            endpointSideColor (input, endpoint)) =
        NormalizationCompiler.firstNormalizedPort input endpoint :=
    firstPortFromData_endpoint (input, endpoint)
  rw [activeEq, portEq]

@[simp] theorem endpointHeaderData_finalChoice
    (input : NormalizationCompiler.Input)
    (endpoint : ContractedEndpoint) :
    (endpointHeaderData input endpoint).finalChoice =
      { active := NormalizationCompiler.secondRotationActive
          input endpoint.vertex
        port := NormalizationCompiler.secondNormalizedPort
          input endpoint } := by
  change RotationTemplateChoice.mk _ _ = RotationTemplateChoice.mk _ _
  congr 1
  · rw [show (endpointHeaderData input endpoint).rotationCount =
        NormalizationCompiler.rotationCountAt input endpoint.vertex from
      endpointHeaderData_rotationCount input endpoint]
    rfl
  · exact endpointHeaderData_secondPort input endpoint

/-- The request header is a finite lookup from the compressed data at its
two endpoints. -/
theorem ofEdge_header_eq_ofEndpointData
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header =
      Header.ofEndpointData
        (endpointHeaderData input (.source edge))
        (endpointHeaderData input (.target edge)) := by
  unfold Header.ofEndpointData
  rw [endpointHeaderData_firstChoice input (.source edge),
    endpointHeaderData_firstChoice input (.target edge),
    endpointHeaderData_secondChoice input (.source edge),
    endpointHeaderData_secondChoice input (.target edge),
    endpointHeaderData_finalChoice input (.source edge),
    endpointHeaderData_finalChoice input (.target edge)]
  rfl

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
