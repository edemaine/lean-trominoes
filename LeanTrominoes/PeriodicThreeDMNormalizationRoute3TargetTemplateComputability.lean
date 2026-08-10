import LeanTrominoes.PeriodicThreeDMNormalizationRoute3SourceTemplateComputability

/-! # Primitive-recursive final-round target templates -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute3TargetTemplate
    (input : Input × ContractedEdge) : List Cell :=
  finalNormalizationTemplate input.1 (.target input.2)

theorem normalizationRoute3TargetTemplate_primrec :
    Primrec normalizationRoute3TargetTemplate := by
  have endpoint : Primrec fun input : Input × ContractedEdge =>
      ContractedEndpoint.target input.2 :=
    contractedEdge_targetEndpoint_primrec.comp Primrec.snd
  exact (finalNormalizationTemplate_primrec.comp
    (Primrec.pair Primrec.fst endpoint)).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
