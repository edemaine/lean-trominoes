import LeanTrominoes.PeriodicThreeDMNormalizationSecondRoundComputability

/-!
# Computability of the final cyclic endpoint-normalization round
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

def finalRoundFromData (input : RotationEndpointData) :
    CanonicalVertexPort × List Cell :=
  let firstPort := firstPortFromData (input.2.1, input.2.2)
  let secondPort :=
    (rotationRoundPortAndRoute
      (firstRotationActiveFromCount input.1) firstPort).1
  rotationRoundPortAndRoute
    (secondRotationActiveFromCount input.1) secondPort

theorem finalRoundFromData_primrec :
    Primrec finalRoundFromData :=
  Primrec.dom_finite _

def finalRoundData (input : Input × ContractedEndpoint) :
    CanonicalVertexPort × List Cell :=
  rotationRoundPortAndRoute
    (secondRotationActive input.1 input.2.vertex)
    (secondNormalizedPort input.1 input.2)

theorem finalRoundData_primrec :
    Primrec finalRoundData := by
  exact (finalRoundFromData_primrec.comp
    rotationEndpointDataAt_primrec).of_eq
      fun input => by
        unfold finalRoundFromData finalRoundData secondNormalizedPort
          rotationEndpointDataAt endpointControlDataAt
          secondRotationActiveFromCount secondRotationActive
          firstRotationActiveFromCount firstRotationActive
        rw [firstPortFromData_endpoint input]

theorem finalNormalizedPort_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      finalNormalizedPort input.1 input.2 :=
  (Primrec.fst.comp finalRoundData_primrec).of_eq fun _ => rfl

theorem finalNormalizationTemplate_primrec :
    Primrec fun input : Input × ContractedEndpoint =>
      finalNormalizationTemplate input.1 input.2 :=
  (Primrec.snd.comp finalRoundData_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
