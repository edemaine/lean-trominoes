/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointControlDataComputability

/-!
# Primitive-recursive endpoint rotation data

Add the vertex rotation count to the endpoint control-data record.
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

abbrev RotationEndpointData :=
  PortRotationCount × EndpointControlData

def rotationEndpointDataAt
    (input : Input × ContractedEndpoint) : RotationEndpointData :=
  (rotationCountAt input.1 input.2.vertex, endpointControlDataAt input)

def rotationEndpointDataFrom
    (input : Bool × EndpointControlData) : RotationEndpointData :=
  (rotationCountFromData (input.1, input.2.1), input.2)

theorem rotationEndpointDataFrom_primrec :
    Primrec rotationEndpointDataFrom :=
  Primrec.dom_finite _

theorem rotationEndpointDataAt_primrec :
    Primrec rotationEndpointDataAt := by
  have vertex : Primrec fun input : Input × ContractedEndpoint =>
      input.2.vertex :=
    contractedEndpoint_vertex_primrec.comp Primrec.snd
  have isTriple : Primrec fun input : Input × ContractedEndpoint =>
      vertexIsTriple input.2.vertex :=
    vertexIsTriple_primrec.comp vertex
  exact (rotationEndpointDataFrom_primrec.comp
    (Primrec.pair isTriple endpointControlDataAt_primrec)).of_eq
      fun input => by
        unfold rotationEndpointDataFrom rotationEndpointDataAt
          endpointControlDataAt
        rw [rotationCountFromData_at (input.1, input.2.vertex)]

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
