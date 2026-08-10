import LeanTrominoes.PeriodicThreeDMNormalizationRoute1SourcePositionComputability

/-!
# Primitive-recursive first-round route endpoint positions
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1Positions
    (input : Input × ContractedEdge) : Cell × Cell :=
  (normalizationPosition0 input.1 input.2.toPeriodicEdge.source,
    normalizationTarget0 input.1 input.2)

theorem normalizationRoute1Positions_primrec :
    Primrec normalizationRoute1Positions := by
  exact (Primrec.pair normalizationRoute1SourcePosition_primrec
    normalizationTarget0_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
