/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationPositionComputability

/-!
# Computability of contracted target prototype positions
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationTargetVertexPosition
    (input : Input × ContractedEdge) : Cell :=
  normalizationPosition0 input.1 input.2.toPeriodicEdge.target

theorem normalizationTargetVertexPosition_primrec :
    Primrec normalizationTargetVertexPosition := by
  have periodicEdge : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge :=
    contractedEdge_toPeriodicEdge_primrec.comp Primrec.snd
  have target : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge.target :=
    periodicEdge_target_primrec.comp periodicEdge
  exact (normalizationPosition0_primrec.comp
    (Primrec.pair Primrec.fst target)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
