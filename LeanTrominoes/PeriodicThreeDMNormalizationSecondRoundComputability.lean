/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRotationEndpointDataComputability

/-!
# Computability of the first cyclic endpoint-normalization round
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

def secondRoundFromData (input : RotationEndpointData) :
    CanonicalVertexPort × List Cell :=
  rotationRoundPortAndRoute
    (firstRotationActiveFromCount input.1)
    (firstPortFromData (input.2.1, input.2.2))

theorem secondRoundFromData_primrec :
    Primrec secondRoundFromData :=
  Primrec.dom_finite _

def secondRoundData (input : Input × ContractedEndpoint) :
    CanonicalVertexPort × List Cell :=
  rotationRoundPortAndRoute
    (firstRotationActive input.1 input.2.vertex)
    (firstNormalizedPort input.1 input.2)

theorem secondRoundData_primrec :
    Primrec secondRoundData := by
  exact (secondRoundFromData_primrec.comp
    rotationEndpointDataAt_primrec).of_eq
      fun input => by
        unfold secondRoundFromData secondRoundData
          rotationEndpointDataAt endpointControlDataAt
          firstRotationActiveFromCount firstRotationActive
        rw [firstPortFromData_endpoint input]

theorem secondNormalizedPort_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      secondNormalizedPort input.1 input.2 :=
  (Primrec.fst.comp secondRoundData_primrec).of_eq fun _ => rfl

theorem secondNormalizationTemplate_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      secondNormalizationTemplate input.1 input.2 :=
  (Primrec.snd.comp secondRoundData_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
