/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute1TargetTemplateComputability

/-!
# Primitive-recursive first-round route template pairs
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1Templates
    (input : Input × ContractedEdge) : List Cell × List Cell :=
  (firstNormalizationTemplate input.1 (.source input.2),
    firstNormalizationTemplate input.1 (.target input.2))

theorem normalizationRoute1Templates_primrec :
    Primrec normalizationRoute1Templates := by
  exact (Primrec.pair normalizationRoute1SourceTemplate_primrec
    normalizationRoute1TargetTemplate_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
