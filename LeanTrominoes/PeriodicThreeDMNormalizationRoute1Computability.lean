import LeanTrominoes.PeriodicThreeDMNormalizationRoute1InputComputability

/-!
# Computability of first-round normalized routes
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationRoute1_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationRoute1 input.1 input.2 :=
  (normalizeRouteWithTemplates_primrec.comp
    normalizationRoute1Input_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
