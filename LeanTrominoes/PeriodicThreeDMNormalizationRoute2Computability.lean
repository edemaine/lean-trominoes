import LeanTrominoes.PeriodicThreeDMNormalizationRoute2TargetTemplateComputability

/-! # Computability of second-round normalized routes -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute2Templates
    (input : Input × ContractedEdge) : List Cell × List Cell :=
  (normalizationRoute2SourceTemplate input,
    normalizationRoute2TargetTemplate input)

theorem normalizationRoute2Templates_primrec :
    Primrec normalizationRoute2Templates :=
  (Primrec.pair normalizationRoute2SourceTemplate_primrec
    normalizationRoute2TargetTemplate_primrec).of_eq fun _ => rfl

def normalizationRoute2LocalData
    (input : Input × ContractedEdge) :
    (Cell × Cell) × (List Cell × List Cell) :=
  (normalizationRoute2Positions input, normalizationRoute2Templates input)

theorem normalizationRoute2LocalData_primrec :
    Primrec normalizationRoute2LocalData :=
  (Primrec.pair normalizationRoute2Positions_primrec
    normalizationRoute2Templates_primrec).of_eq fun _ => rfl

def normalizationRoute2Input
    (input : Input × ContractedEdge) : NormalizeRouteInput :=
  (normalizationRoute2LocalData input,
    normalizationRoute1 input.1 input.2)

theorem normalizationRoute2Input_primrec :
    Primrec normalizationRoute2Input :=
  (Primrec.pair normalizationRoute2LocalData_primrec
    normalizationRoute1_primrec).of_eq fun _ => rfl

theorem normalizationRoute2_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationRoute2 input.1 input.2 :=
  (normalizeRouteWithTemplates_primrec.comp
    normalizationRoute2Input_primrec).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
