import LeanTrominoes.PeriodicThreeDMNormalizationTargetTranslationComputability

/-!
# Computability of initial normalized target occurrences
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationTarget0_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationTarget0 input.1 input.2 := by
  exact (cell_add_primrec.comp
    normalizationTargetVertexPosition_primrec
    normalizationEdgeTranslation_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
