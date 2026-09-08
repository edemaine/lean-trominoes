/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatch
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestThreeRoundCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Inner compiler for one delimited normalization request -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Batch

open Computability Turing

/-- Output alphabet retaining one delimiter after every normalized route. -/
inductive NormalizedToken
  | direction (value : AxisDirection)
  | routeEnd
  deriving DecidableEq, Fintype, Repr

-- An explicit default avoids a code-generation failure in the derived instance.
instance : Inhabited NormalizedToken := ⟨.routeEnd⟩

def untagBlock : Batch.Token → List NormalizationDirectionRequest.Token
  | .request token => [token]
  | .requestEnd => []

def untagged (block : List Batch.Token) :
    List NormalizationDirectionRequest.Token :=
  block.flatMap untagBlock

@[simp]
theorem untagged_requestBlock (request : Request) :
    untagged (requestBlock request) = request.tokens := by
  unfold untagged requestBlock
  simp [untagBlock, List.flatMap_map]

noncomputable def untaggedComputableInPolyTime :
    TM2ComputableInPolyTime id id untagged := by
  change TM2ComputableInPolyTime id id
    (fun block : List Batch.Token => block.flatMap untagBlock)
  exact FiniteBlockTransducer.computableInPolyTime untagBlock

namespace Finalizer

def transition (_ : Unit) (direction : AxisDirection) :
    Unit × List NormalizedToken :=
  ((), [.direction direction])

def finish (_ : Unit) : List NormalizedToken := [.routeEnd]

def output (directions : List AxisDirection) : List NormalizedToken :=
  FiniteStateTransducer.output () transition finish directions

@[simp]
theorem scan (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition () directions =
      ((), directions.map NormalizedToken.direction) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

@[simp]
theorem output_eq (directions : List AxisDirection) :
    output directions =
      directions.map NormalizedToken.direction ++ [.routeEnd] := by
  simp [output, FiniteStateTransducer.output, finish]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output () transition finish)
  exact FiniteStateTransducer.computableInPolyTime () transition finish

end Finalizer

/-- Physical one-block pipeline: remove the outer tags, normalize the inner
request three times, and restore one output route delimiter. -/
def innerOutput (block : List Batch.Token) : List NormalizedToken :=
  Finalizer.output (threeRoundDirectionsOutput (untagged block))

def normalizedBlock (request : Request) : List NormalizedToken :=
  (normalizeThreeRounds request).directions.map .direction ++ [.routeEnd]

@[simp]
theorem innerOutput_requestBlock (request : Request) :
    innerOutput (requestBlock request) = normalizedBlock request := by
  unfold innerOutput normalizedBlock
  rw [untagged_requestBlock, threeRoundDirectionsOutput_request,
    Finalizer.output_eq]

noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  let untag := untaggedComputableInPolyTime
  let normalized := TM2CompositionMachine.computableInPolyTime untag
    threeRoundDirectionsOutputComputableInPolyTime
  let finalized := TM2CompositionMachine.computableInPolyTime normalized
    Finalizer.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun block => Finalizer.output
      (threeRoundDirectionsOutput (untagged block)))
  exact finalized

end Batch
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
