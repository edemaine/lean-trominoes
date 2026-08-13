/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationTargetTranslationComputability

/-!
# Computability of initial normalized target occurrences
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationTarget0_primrec :
    Primrec fun input : Input × ContractedEdge =>
      normalizationTarget0 input.1 input.2 := by
  exact (cell_add_primrec.comp
    normalizationTargetVertexPosition_primrec
    normalizationEdgeTranslation_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
