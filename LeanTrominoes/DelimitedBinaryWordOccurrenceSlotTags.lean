/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords

/-! # Fixed occurrence-slot tags for delimited binary words -/

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

/-- Every route descriptor reserves one slot for each of the at most
`9 * 9 = 81` neighboring segment occurrences. -/
abbrev Slot := Fin 81

/-- Append a twelfth unary field encoding the occurrence-slot index. -/
def slotWord (slot : Slot) (word : List Bool) : List Bool :=
  word ++ List.replicate slot.val false ++ [true]

/-- Expand every semantic word into its eighty-one slot-tagged copies. -/
def expandInput (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.flatMap fun word =>
    (List.finRange 81).map fun slot => slotWord slot word⟩

/-- Per-symbol substitution that inserts a slot tag immediately before the
word-end delimiter. -/
def slotTagSubstitution (slot : Slot) :
    DelimitedBinaryWords.Token → List DelimitedBinaryWords.Token
  | .wordEnd =>
      List.replicate slot.val (.bit false) ++ [.bit true, .wordEnd]
  | token => [token]

/-- Insert one fixed slot tag into a complete physical word block. -/
def taggedCopy (slot : Slot) (tokens : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  tokens.flatMap (slotTagSubstitution slot)

/-- Concatenate all eighty-one tagged copies of one physical word block. -/
def taggedCopies (tokens : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  (List.finRange 81).flatMap fun slot => taggedCopy slot tokens

/-- Inserting one tag into a canonical physical word produces the canonical
encoding of the corresponding slot-tagged semantic word. -/
@[simp] theorem taggedCopy_wordTokens (slot : Slot) (word : List Bool) :
    taggedCopy slot (DelimitedBinaryWords.wordTokens word) =
      DelimitedBinaryWords.wordTokens (slotWord slot word) := by
  have bits :
      (word.map DelimitedBinaryWords.Token.bit).flatMap
          (slotTagSubstitution slot) =
        word.map DelimitedBinaryWords.Token.bit := by
    induction word with
    | nil => rfl
    | cons bit word induction =>
        simp [slotTagSubstitution, induction]
  simp [taggedCopy, slotTagSubstitution, DelimitedBinaryWords.wordTokens,
    slotWord, List.map_append, bits]

/-- The physical copies of one canonical word are exactly its eighty-one
canonical slot-tagged encodings, in increasing slot order. -/
@[simp] theorem taggedCopies_wordTokens (word : List Bool) :
    taggedCopies (DelimitedBinaryWords.wordTokens word) =
      (List.finRange 81).flatMap fun slot =>
        DelimitedBinaryWords.wordTokens (slotWord slot word) := by
  simp [taggedCopies]

/-- Expanding all physical word blocks agrees exactly with the semantic
eighty-one-copy expansion. -/
theorem flatMap_taggedCopies_wordTokens
    (input : DelimitedBinaryWords.Input) :
    input.words.flatMap (fun word =>
        taggedCopies (DelimitedBinaryWords.wordTokens word)) =
      DelimitedBinaryWords.encode (expandInput input) := by
  rcases input with ⟨words⟩
  simp only [taggedCopies_wordTokens]
  unfold DelimitedBinaryWords.encode expandInput
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro word _
  rw [List.flatMap_map]

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes
