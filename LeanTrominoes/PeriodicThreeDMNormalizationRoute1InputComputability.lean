import LeanTrominoes.PeriodicThreeDMNormalizationRoute1TemplatesComputability

/-!
# Primitive-recursive first-round route compiler input
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1LocalData
    (input : Input × ContractedEdge) :
    (Cell × Cell) × (List Cell × List Cell) :=
  (normalizationRoute1Positions input, normalizationRoute1Templates input)

theorem normalizationRoute1LocalData_primrec :
    Primrec normalizationRoute1LocalData :=
  (Primrec.pair normalizationRoute1Positions_primrec
    normalizationRoute1Templates_primrec).of_eq fun _ => rfl

def normalizationRoute1Input
    (input : Input × ContractedEdge) : NormalizeRouteInput :=
  (normalizationRoute1LocalData input,
    contractedEdgeRoute input.1 input.2)

theorem normalizationRoute1Input_primrec :
    Primrec normalizationRoute1Input := by
  have oldRoute : Primrec fun input : Input × ContractedEdge =>
      contractedEdgeRoute input.1 input.2 :=
    contractedEdgeRoute_primrec
  exact (Primrec.pair normalizationRoute1LocalData_primrec
    oldRoute).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
