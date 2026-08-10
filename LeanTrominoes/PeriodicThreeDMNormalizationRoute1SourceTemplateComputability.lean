import LeanTrominoes.PeriodicThreeDMNormalizationRoute1PositionsComputability

/-!
# Primitive-recursive first-round source templates
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1SourceTemplate
    (input : Input × ContractedEdge) : List Cell :=
  firstNormalizationTemplate input.1 (.source input.2)

theorem normalizationRoute1SourceTemplate_primrec :
    Primrec normalizationRoute1SourceTemplate := by
  have endpoint : Primrec fun input : Input × ContractedEdge =>
      ContractedEndpoint.source input.2 :=
    contractedEdge_sourceEndpoint_primrec.comp Primrec.snd
  exact (firstNormalizationTemplate_primrec.comp
    (Primrec.pair Primrec.fst endpoint)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
