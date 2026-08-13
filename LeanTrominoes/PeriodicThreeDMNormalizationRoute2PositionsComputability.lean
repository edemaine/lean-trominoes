/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute2SourcePositionComputability

/-! # Primitive-recursive second-round route endpoint positions -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute2Positions
    (input : Input × ContractedEdge) : Cell × Cell :=
  (normalizationRoute2SourcePosition input,
    normalizationTarget1 input.1 input.2)

theorem normalizationRoute2Positions_primrec :
    Primrec normalizationRoute2Positions :=
  (Primrec.pair normalizationRoute2SourcePosition_primrec
    normalizationTarget1_primrec).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
