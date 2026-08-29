/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterCompiler
import LeanTrominoes.BinaryRouteTailRecordFormatterSemantics

/-! # Semantics of batched binary route-tail formatting -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordBatchFormatter

open FiniteStateTransducer

private theorem scan_sourceTokens
    (firstProfile secondProfile : Profile)
    (control : BinaryRouteTailRecordFormatter.Control)
    (input : List SourceToken) :
    scan transition ⟨firstProfile, secondProfile, control⟩
        (input.map Token.source) =
      let result := scan
        (BinaryRouteTailRecordFormatter.transition
          firstProfile secondProfile)
        control input
      (⟨firstProfile, secondProfile, result.1⟩, result.2) := by
  induction input generalizing control with
  | nil => rfl
  | cons token input induction =>
      simp only [List.map_cons, scan, transition]
      generalize stepEq :
        BinaryRouteTailRecordFormatter.transition
          firstProfile secondProfile control token = step
      rcases step with ⟨next, emitted⟩
      simp only
      rw [induction next]

/-- Every framed four-route block resets the delegated scan and emits its
two binary-clause records, independently of the preceding control state. -/
theorem scan_blockTokens (state : State) (block : Block) :
    scan transition state (blockTokens block) =
      (⟨block.firstProfile, block.secondProfile,
          BinaryRouteTailRecordFormatter.Control.done⟩,
        block.records) := by
  unfold blockTokens sourceTokens Block.records
  simp only [scan, transition]
  rw [← List.map_append, ← List.map_append, ← List.map_append]
  rw [scan_sourceTokens]
  rw [BinaryRouteTailRecordFormatter.scan_four_routes]
  rfl

/-- Scanning a canonical block stream emits exactly the concatenated record
stream, regardless of the control state preceding its first block. -/
theorem scan_tokens_records (state : State) (blocks : List Block) :
    (scan transition state (tokens blocks)).2 = records blocks := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block blocks induction =>
      change
        (scan transition state
          (blockTokens block ++ tokens blocks)).2 =
        block.records ++ records blocks
      rw [scan_append, scan_blockTokens]
      dsimp only
      rw [induction]

/-- The batched finite-state wrapper formats every canonical block
independently and preserves presentation order. -/
@[simp] theorem output_tokens (blocks : List Block) :
    output (tokens blocks) = records blocks := by
  unfold output FiniteStateTransducer.output
  change
    (scan transition initial (tokens blocks)).2 ++
        finish (scan transition initial (tokens blocks)).1 =
      records blocks
  rw [scan_tokens_records]
  simp [finish]

end BinaryRouteTailRecordBatchFormatter
end LeanTrominoes
