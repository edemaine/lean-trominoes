/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRotationComputability

/-!
# Computability of first-round normalized endpoint ports

Compute the first canonical port and local direction-normalization template
from compressed fan and endpoint data.  This module also computes the two
rotation-round activation flags.
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

def omittedSideFromData : Option EndpointTripleData → VertexSide
  | none => .east
  | some data => omittedSide data.1.1 data.2.1.1 data.2.2.1

theorem omittedSideFromData_primrec :
    Primrec omittedSideFromData :=
  Primrec.dom_finite _

def firstPortFromData
    (input : Option EndpointTripleData × EndpointSideColor) :
    CanonicalVertexPort :=
  canonicalPortForSide (omittedSideFromData input.1) input.2.1

theorem firstPortFromData_primrec :
    Primrec firstPortFromData :=
  Primrec.dom_finite _

def firstTemplateFromData
    (input : Option EndpointTripleData × EndpointSideColor) : List Cell :=
  let omitted := omittedSideFromData input.1
  route omitted (canonicalPortForSide omitted input.2.1)

theorem firstTemplateFromData_primrec :
    Primrec firstTemplateFromData :=
  Primrec.dom_finite _

theorem firstPortFromData_endpoint
    (input : Input × ContractedEndpoint) :
    firstPortFromData
        (endpointTripleDataAt (input.1, input.2.vertex),
          endpointSideColor input) =
      firstNormalizedPort input.1 input.2 := by
  rcases input with ⟨compilerInput, endpoint⟩
  unfold firstPortFromData omittedSideFromData endpointTripleDataAt
    endpointSideColor firstNormalizedPort omittedSideAt
  cases compilerInput.problem.endpointTripleAt endpoint.vertex with
  | none => rfl
  | some endpoints =>
      rcases endpoints with ⟨first, second, third⟩
      rfl

theorem firstNormalizedPort_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      firstNormalizedPort input.1 input.2 := by
  have vertex : Primrec fun input : Input × ContractedEndpoint =>
      input.2.vertex :=
    contractedEndpoint_vertex_primrec.comp Primrec.snd
  have fanData : Primrec fun input : Input × ContractedEndpoint =>
      endpointTripleDataAt (input.1, input.2.vertex) :=
    endpointTripleDataAt_primrec.comp
      (Primrec.pair Primrec.fst vertex)
  have endpointData : Primrec fun input : Input × ContractedEndpoint =>
      endpointSideColor input :=
    endpointSideColor_primrec
  exact (firstPortFromData_primrec.comp
    (Primrec.pair fanData endpointData)).of_eq
      firstPortFromData_endpoint

theorem firstNormalizationTemplate_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      firstNormalizationTemplate input.1 input.2 := by
  have vertex : Primrec fun input : Input × ContractedEndpoint =>
      input.2.vertex :=
    contractedEndpoint_vertex_primrec.comp Primrec.snd
  have fanData : Primrec fun input : Input × ContractedEndpoint =>
      endpointTripleDataAt (input.1, input.2.vertex) :=
    endpointTripleDataAt_primrec.comp
      (Primrec.pair Primrec.fst vertex)
  have endpointData : Primrec fun input : Input × ContractedEndpoint =>
      endpointSideColor input :=
    endpointSideColor_primrec
  exact (firstTemplateFromData_primrec.comp
    (Primrec.pair fanData endpointData)).of_eq fun input => by
      rcases input with ⟨compilerInput, endpoint⟩
      unfold firstTemplateFromData omittedSideFromData endpointTripleDataAt
        endpointSideColor firstNormalizationTemplate firstNormalizedPort
        omittedSideAt
      cases compilerInput.problem.endpointTripleAt endpoint.vertex with
      | none => rfl
      | some endpoints =>
          rcases endpoints with ⟨first, second, third⟩
          rfl

def firstRotationActiveFromCount (count : PortRotationCount) : Bool :=
  count != .zero

def secondRotationActiveFromCount (count : PortRotationCount) : Bool :=
  count == .two

theorem firstRotationActiveFromCount_primrec :
    Primrec firstRotationActiveFromCount :=
  Primrec.dom_finite _

theorem secondRotationActiveFromCount_primrec :
    Primrec secondRotationActiveFromCount :=
  Primrec.dom_finite _

theorem firstRotationActive_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      firstRotationActive input.1 input.2 := by
  exact (firstRotationActiveFromCount_primrec.comp
    rotationCountAt_primrec).of_eq fun _ => rfl

theorem secondRotationActive_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      secondRotationActive input.1 input.2 := by
  exact (secondRotationActiveFromCount_primrec.comp
    rotationCountAt_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
