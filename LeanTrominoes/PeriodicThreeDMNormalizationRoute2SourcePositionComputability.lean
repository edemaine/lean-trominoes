import LeanTrominoes.PeriodicThreeDMNormalizationRoute1Computability

/-! # Primitive-recursive second-round route source positions -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute2SourcePosition
    (input : Input × ContractedEdge) : Cell :=
  normalizationPosition1 input.1 input.2.toPeriodicEdge.source

theorem normalizationRoute2SourcePosition_primrec :
    Primrec normalizationRoute2SourcePosition := by
  have source : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge.source :=
    contractedEdge_sourceVertex_primrec.comp Primrec.snd
  exact (normalizationPosition1_primrec.comp
    (Primrec.pair Primrec.fst source)).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
