/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoute2Computability

/-! # Primitive-recursive final-round route source positions -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationRoute3SourcePosition
    (input : Input × ContractedEdge) : Cell :=
  normalizationPosition2 input.1 input.2.toPeriodicEdge.source

theorem normalizationRoute3SourcePosition_primrec :
    Primrec normalizationRoute3SourcePosition := by
  have source : Primrec fun input : Input × ContractedEdge =>
      input.2.toPeriodicEdge.source :=
    contractedEdge_sourceVertex_primrec.comp Primrec.snd
  exact (normalizationPosition2_primrec.comp
    (Primrec.pair Primrec.fst source)).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
