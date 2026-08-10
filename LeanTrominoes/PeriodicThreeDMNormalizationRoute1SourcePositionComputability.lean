import LeanTrominoes.PeriodicThreeDMNormalizationEdgeComputability

/-!
# Primitive-recursive first-round route source positions
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1SourcePosition
    (input : Input × ContractedEdge) : Cell :=
  normalizationPosition0 input.1 input.2.toPeriodicEdge.source

theorem normalizationRoute1SourcePosition_primrec :
    Primrec normalizationRoute1SourcePosition := by
  have source : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge.source :=
    contractedEdge_sourceVertex_primrec.comp Primrec.snd
  exact (normalizationPosition0_primrec.comp
    (Primrec.pair Primrec.fst source)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
