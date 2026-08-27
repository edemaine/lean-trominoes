/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionRequestData
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler boundary for direct route-normalization requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM.NormalizationDirectionRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteDirectionRequestCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Sole source-side emitter still needed before the uniform dynamic
three-round route machine can run on the direct PSPACE source word. -/
abbrev DirectSparseRouteDirectionRequestTokenCompiler :=
  TM2ComputableInPolyTime id id
    (directSparseRouteDirectionRequestTokensOfSymbols decider)

/-- Any exact request emitter composes with the fully concrete batch
normalizer to produce all final route direction words and boundaries. -/
noncomputable def directSparseNormalizedRouteDirectionTokensComputableInPolyTime
    (requests : DirectSparseRouteDirectionRequestTokenCompiler decider) :
    TM2ComputableInPolyTime id id
      (fun symbols => Batch.normalizedOutput
        (directSparseRouteDirectionRequestTokensOfSymbols decider symbols)) :=
  TM2CompositionMachine.computableInPolyTime requests
    Batch.normalizedOutputComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
