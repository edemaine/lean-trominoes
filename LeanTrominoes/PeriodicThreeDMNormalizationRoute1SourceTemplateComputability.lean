/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute1PositionsComputability

/-!
# Primitive-recursive first-round source templates
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute1SourceTemplate
    (input : Input × ContractedEdge) : List Cell :=
  firstNormalizationTemplate input.1 (.source input.2)

theorem normalizationRoute1SourceTemplate_primrec :
    Primrec normalizationRoute1SourceTemplate := by
  have endpoint : Primrec fun input : Input × ContractedEdge =>
      ContractedEndpoint.source input.2 :=
    contractedEdge_sourceEndpoint_primrec.comp Primrec.snd
  exact (firstNormalizationTemplate_primrec.comp
    (Primrec.pair Primrec.fst endpoint)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
