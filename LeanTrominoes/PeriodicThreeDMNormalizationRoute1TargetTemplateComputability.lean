/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute1SourceTemplateComputability

/-!
# Primitive-recursive first-round target templates
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1TargetTemplate
    (input : Input × ContractedEdge) : List Cell :=
  firstNormalizationTemplate input.1 (.target input.2)

theorem normalizationRoute1TargetTemplate_primrec :
    Primrec normalizationRoute1TargetTemplate := by
  have endpoint : Primrec fun input : Input × ContractedEdge =>
      ContractedEndpoint.target input.2 :=
    contractedEdge_targetEndpoint_primrec.comp Primrec.snd
  exact (firstNormalizationTemplate_primrec.comp
    (Primrec.pair Primrec.fst endpoint)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
