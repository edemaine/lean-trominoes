/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionRequestBatch
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for batched horizontal typed incidence requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceDirectionRequest
namespace Batch

open Computability Turing

noncomputable def untaggedComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun block : List Token => block.flatMap untagBlock) := by
  exact FiniteBlockTransducer.computableInPolyTime untagBlock

noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  let complete := TM2CompositionMachine.computableInPolyTime
    untaggedComputableInPolyTime
    HorizontalTypedIncidenceDirectionRequest.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun block => HorizontalTypedIncidenceDirectionRequest.output
      (block.flatMap untagBlock))
  exact complete

/-- Map the verified compact request compiler independently over all incidence
boundaries. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime isEnd

end Batch
end HorizontalTypedIncidenceDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
