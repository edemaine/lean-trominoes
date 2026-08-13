/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationTargetPositionComputability

/-!
# Computability of contracted target period translations
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem periodicEdge_offset_primrec :
    Primrec (PeriodicEdge.offset :
      PeriodicEdge PeriodicThreeDMVertex → Cell) := by
  have forward : Primrec
      (@PeriodicEdge.equivData PeriodicThreeDMVertex) :=
    Primrec.of_equiv
  exact ((Primrec.snd.comp Primrec.snd).comp forward).of_eq
    fun _ => rfl

def normalizationEdgeTranslation
    (input : Input × ContractedEdge) : Cell :=
  (contractedDrawing input.1).periodTranslation
    input.2.toPeriodicEdge.offset

theorem normalizationEdgeTranslation_primrec :
    Primrec normalizationEdgeTranslation := by
  have periodicEdge : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge :=
    contractedEdge_toPeriodicEdge_primrec.comp Primrec.snd
  have offset : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge.offset :=
    periodicEdge_offset_primrec.comp periodicEdge
  exact (periodTranslation_primrec.comp
    (contractedDrawing_primrec.comp Primrec.fst) offset).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
