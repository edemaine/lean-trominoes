import LeanTrominoes.PeriodicThreeDMNormalizationRoute3SourcePositionComputability

/-! # Primitive-recursive final-round route endpoint positions -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute3Positions
    (input : Input × ContractedEdge) : Cell × Cell :=
  (normalizationRoute3SourcePosition input,
    normalizationTarget2 input.1 input.2)

theorem normalizationRoute3Positions_primrec :
    Primrec normalizationRoute3Positions :=
  (Primrec.pair normalizationRoute3SourcePosition_primrec
    normalizationTarget2_primrec).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
