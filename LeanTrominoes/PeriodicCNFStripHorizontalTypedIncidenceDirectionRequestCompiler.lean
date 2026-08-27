/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionRequestData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for complete horizontal typed incidence requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceDirectionRequest

open Computability Turing

abbrev Token := HorizontalOccurrenceDirectionRequest.Token
abbrev NormalizedToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

/-- Compile one compact typed-incidence request and restore one route
delimiter after its exact direction word. -/
def output (request : List Token) : List NormalizedToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output
    (HorizontalOccurrenceDirectionRequest.output request)

/-- Every classified block compiles to its exact directions followed by one
incidence boundary. -/
@[simp] theorem output_requestTokens
    (block : HorizontalTypedIncidenceDirectionBlock) :
    output block.requestTokens =
      block.directions.map .direction ++ [.routeEnd] := by
  unfold output
  rw [PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output_eq,
    HorizontalTypedIncidenceDirectionBlock.output_requestTokens]

/-- Composition of the occurrence request transducer and the existing
direction finalizer compiles one typed incidence in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  let complete := TM2CompositionMachine.computableInPolyTime
    HorizontalOccurrenceDirectionRequest.computableInPolyTime
    PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun request =>
      PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output
        (HorizontalOccurrenceDirectionRequest.output request))
  exact complete

end HorizontalTypedIncidenceDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
