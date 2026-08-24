/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotTagCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for all fixed delimited binary-word occurrence slots -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

open Computability Turing

/-- Concatenate the tagged copies selected by a fixed slot list. -/
def taggedCopiesFor (slots : List Slot)
    (tokens : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  slots.flatMap fun slot => taggedCopy slot tokens

/-- A fixed list of slot-tagged copies is polynomial-time computable. -/
noncomputable def taggedCopiesForComputableInPolyTime :
    (slots : List Slot) →
      TM2ComputableInPolyTime id id (taggedCopiesFor slots)
  | [] => by
      change TM2ComputableInPolyTime id id
        (fun _ : List DelimitedBinaryWords.Token => [])
      let empty := FiniteBlockTransducer.computableInPolyTime
        (fun _ : DelimitedBinaryWords.Token =>
          ([] : List DelimitedBinaryWords.Token))
      refine
        { tm := empty.tm
          inputAlphabet := empty.inputAlphabet
          outputAlphabet := empty.outputAlphabet
          time := empty.time
          outputsFun := ?_ }
      intro tokens
      have outputEq :
          tokens.flatMap (fun _ : DelimitedBinaryWords.Token =>
            ([] : List DelimitedBinaryWords.Token)) = [] := by
        induction tokens with
        | nil => rfl
        | cons _ tokens induction => exact induction
      have run := empty.outputsFun tokens
      rw [outputEq] at run
      exact run
  | slot :: slots => by
      change TM2ComputableInPolyTime id id
        (fun tokens =>
          taggedCopy slot tokens ++ taggedCopiesFor slots tokens)
      exact TM2ListAppend.computableInPolyTime
        (taggedCopyComputableInPolyTime slot)
        (taggedCopiesForComputableInPolyTime slots)

/-- The concrete eighty-one-copy operation is the generic fixed-list
operation at the complete slot range. -/
theorem taggedCopies_eq_taggedCopiesFor
    (tokens : List DelimitedBinaryWords.Token) :
    taggedCopies tokens = taggedCopiesFor (List.finRange 81) tokens := by
  rfl

/-- Producing all eighty-one slot-tagged copies is polynomial-time. -/
noncomputable def taggedCopiesComputableInPolyTime :
    TM2ComputableInPolyTime id id taggedCopies := by
  change TM2ComputableInPolyTime id id
    (taggedCopiesFor (List.finRange 81))
  exact taggedCopiesForComputableInPolyTime (List.finRange 81)

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes

end
