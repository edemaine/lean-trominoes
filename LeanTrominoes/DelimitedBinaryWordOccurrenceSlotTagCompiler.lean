/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotTags
import LeanTrominoes.FiniteBlockTransducer

/-! # Compiler for one delimited binary-word occurrence-slot tag -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

open Computability Turing

/-- Inserting one fixed occurrence-slot field is a finite block
substitution, hence polynomial-time. -/
noncomputable def taggedCopyComputableInPolyTime (slot : Slot) :
    TM2ComputableInPolyTime id id (taggedCopy slot) := by
  change TM2ComputableInPolyTime id id
    (fun tokens => tokens.flatMap (slotTagSubstitution slot))
  exact FiniteBlockTransducer.computableInPolyTime
    (slotTagSubstitution slot)

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes

end
