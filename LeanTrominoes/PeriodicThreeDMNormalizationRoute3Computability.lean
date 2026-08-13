/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute3TargetTemplateComputability

/-! # Computability of final normalized routes -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute3Templates
    (input : Input × ContractedEdge) : List Cell × List Cell :=
  (normalizationRoute3SourceTemplate input,
    normalizationRoute3TargetTemplate input)

theorem normalizationRoute3Templates_primrec :
    Primrec normalizationRoute3Templates :=
  (Primrec.pair normalizationRoute3SourceTemplate_primrec
    normalizationRoute3TargetTemplate_primrec).of_eq fun _ => rfl

def normalizationRoute3LocalData
    (input : Input × ContractedEdge) :
    (Cell × Cell) × (List Cell × List Cell) :=
  (normalizationRoute3Positions input, normalizationRoute3Templates input)

theorem normalizationRoute3LocalData_primrec :
    Primrec normalizationRoute3LocalData :=
  (Primrec.pair normalizationRoute3Positions_primrec
    normalizationRoute3Templates_primrec).of_eq fun _ => rfl

def normalizationRoute3Input
    (input : Input × ContractedEdge) : NormalizeRouteInput :=
  (normalizationRoute3LocalData input,
    normalizationRoute2 input.1 input.2)

theorem normalizationRoute3Input_primrec :
    Primrec normalizationRoute3Input :=
  (Primrec.pair normalizationRoute3LocalData_primrec
    normalizationRoute2_primrec).of_eq fun _ => rfl

theorem finalNormalizationRoute_primrec :
    Primrec fun input : Input × ContractedEdge =>
      finalNormalizationRoute input.1 input.2 :=
  (normalizeRouteWithTemplates_primrec.comp
    normalizationRoute3Input_primrec).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
