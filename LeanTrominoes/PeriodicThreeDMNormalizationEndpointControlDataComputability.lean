import LeanTrominoes.PeriodicThreeDMNormalizationEndpointPortComputability

/-!
# Primitive-recursive endpoint control data

Package the fan record and the selected endpoint's side/color record.
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

abbrev EndpointControlData :=
  Option EndpointTripleData × EndpointSideColor

def endpointControlDataAt
    (input : Input × ContractedEndpoint) : EndpointControlData :=
  (endpointTripleDataAt (input.1, input.2.vertex), endpointSideColor input)

theorem endpointControlDataAt_primrec :
    Primrec endpointControlDataAt := by
  have vertex : Primrec fun input : Input × ContractedEndpoint =>
      input.2.vertex :=
    contractedEndpoint_vertex_primrec.comp Primrec.snd
  have fanData : Primrec fun input : Input × ContractedEndpoint =>
      endpointTripleDataAt (input.1, input.2.vertex) :=
    endpointTripleDataAt_primrec.comp
      (Primrec.pair Primrec.fst vertex)
  exact (Primrec.pair fanData endpointSideColor_primrec).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
