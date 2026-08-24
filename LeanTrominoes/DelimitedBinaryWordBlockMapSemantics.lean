/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # End-delimited blocks of canonical binary words -/

namespace LeanTrominoes
namespace DelimitedBinaryWords

open TM2EndDelimitedBlockMap

/-- Recognize the final delimiter of a binary word. -/
def isWordEnd : Token → Bool
  | .wordEnd => true
  | _ => false

/-- The portion of a canonical word before its final delimiter. -/
def wordBody (word : List Bool) : List Token :=
  .wordStart :: word.map .bit

theorem wordTokens_eq_body (word : List Bool) :
    wordTokens word = wordBody word ++ [.wordEnd] := by
  simp [wordTokens, wordBody]

theorem wordBody_continues (word : List Bool) :
    ∀ token ∈ wordBody word, isWordEnd token = false := by
  intro token member
  rcases List.mem_cons.mp member with start | bit
  · subst token
    rfl
  · obtain ⟨value, _, rfl⟩ := List.mem_map.mp bit
    rfl

theorem blocksAux_append_wordEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isWordEnd token = false) :
    blocksAux isWordEnd reverseBlock (body ++ .wordEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.wordEnd]) ::
        blocksAux isWordEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil =>
      simp [blocksAux, isWordEnd]
  | cons token body induction =>
      have tokenContinues : isWordEnd token = false :=
        continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isWordEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

theorem blocksAux_wordTokens_append
    (word : List Bool) (rest : List Token) :
    blocksAux isWordEnd [] (wordTokens word ++ rest) =
      wordTokens word :: blocksAux isWordEnd [] rest := by
  rw [wordTokens_eq_body, List.append_assoc]
  exact blocksAux_append_wordEnd [] (wordBody word) rest
    (wordBody_continues word)

theorem blocksAux_encode (words : List (List Bool)) :
    blocksAux isWordEnd [] (words.flatMap wordTokens) =
      words.map wordTokens := by
  induction words with
  | nil => rfl
  | cons word words induction =>
      rw [List.flatMap_cons, blocksAux_wordTokens_append,
        List.map_cons, induction]

@[simp] theorem blocks_encode (input : Input) :
    blocks isWordEnd (encode input) = input.words.map wordTokens := by
  rcases input with ⟨words⟩
  exact blocksAux_encode words

theorem mappedOutput_encode
    {Target : Type} (function : List Token → List Target)
    (input : Input) :
    mappedOutput isWordEnd function (encode input) =
      input.words.flatMap fun word => function (wordTokens word) := by
  unfold mappedOutput
  rw [blocks_encode, List.flatMap_map]

end DelimitedBinaryWords
end LeanTrominoes
