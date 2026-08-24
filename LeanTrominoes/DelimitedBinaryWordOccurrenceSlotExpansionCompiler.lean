/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBlockMapSemantics
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotCopiesCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Compiler for fixed occurrence-slot expansion of binary words -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

open Computability Turing

/-- Expand every complete physical binary-word block into its eighty-one
slot-tagged copies. -/
def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    DelimitedBinaryWords.isWordEnd taggedCopies source

/-- Fixed occurrence-slot expansion of a physical word stream is
polynomial-time. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    taggedCopiesComputableInPolyTime DelimitedBinaryWords.isWordEnd

/-- On canonical input, the physical expander implements exactly the
semantic eighty-one-copy operation. -/
@[simp] theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (expandInput input) := by
  unfold tokens
  rw [DelimitedBinaryWords.mappedOutput_encode]
  exact flatMap_taggedCopies_wordTokens input

/-- Slot expansion exposed at the semantic delimited-word input boundary. -/
def inputTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  tokens (DelimitedBinaryWords.encode input)

/-- The same expander under the canonical semantic input encoding. -/
noncomputable def inputTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id inputTokens :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode
    tokensComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes

end
