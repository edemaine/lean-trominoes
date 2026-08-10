import LeanTrominoes.PeriodicThreeDMNormalizationRouteComputability

/-!
# Primitive-recursive normalized endpoint data

Package each contracted endpoint's outward side together with its wire color.
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

abbrev EndpointTriple :=
  ContractedEndpoint × ContractedEndpoint × ContractedEndpoint

abbrev EndpointSideColor := VertexSide × WireColor

abbrev EndpointTripleData :=
  EndpointSideColor × EndpointSideColor × EndpointSideColor

abbrev AtSide :=
  (Input × PeriodicThreeDMVertex) × VertexSide

/-- The finite local data used by endpoint-color selection. -/
def endpointSideColor
    (input : Input × ContractedEndpoint) : EndpointSideColor :=
  (outwardSide input.1 input.2, input.2.color)

theorem endpointSideColor_primrec :
    Primrec endpointSideColor := by
  exact (Primrec.pair outwardSide_primrec
    (contractedEndpoint_color_primrec.comp Primrec.snd)).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
