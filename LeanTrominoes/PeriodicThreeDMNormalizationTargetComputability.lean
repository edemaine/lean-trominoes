import LeanTrominoes.PeriodicThreeDMNormalizationTarget0Computability

/-!
# Computability of affine normalized target-occurrence rounds
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationTarget1_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationTarget1 input.1 input.2 :=
  (normalizeVertexPosition_primrec.comp
    normalizationTarget0_primrec).of_eq fun _ => rfl

theorem normalizationTarget2_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationTarget2 input.1 input.2 :=
  (normalizeVertexPosition_primrec.comp
    (normalizeVertexPosition_primrec.comp
      normalizationTarget0_primrec)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
