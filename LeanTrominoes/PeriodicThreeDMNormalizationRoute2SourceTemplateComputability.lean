/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute2PositionsComputability

/-! # Primitive-recursive second-round source templates -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute2SourceTemplate
    (input : Input × ContractedEdge) : List Cell :=
  secondNormalizationTemplate input.1 (.source input.2)

theorem normalizationRoute2SourceTemplate_primrec :
    Primrec normalizationRoute2SourceTemplate := by
  have endpoint : Primrec fun input : Input × ContractedEdge =>
      ContractedEndpoint.source input.2 :=
    contractedEdge_sourceEndpoint_primrec.comp Primrec.snd
  exact (secondNormalizationTemplate_primrec.comp
    (Primrec.pair Primrec.fst endpoint)).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
