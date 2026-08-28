/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionData

/-! # Semantics of four-word expansion of binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

open TM2EndDelimitedBlockMap

private def pairBody
    (pair : List Bool × List Bool) : List PairToken :=
  .pairStart ::
    (pair.1.map .firstBit ++ .middle :: pair.2.map .secondBit)

private theorem pairTokens_eq_body
    (pair : List Bool × List Bool) :
    DelimitedBinaryWordPairs.pairTokens pair =
      pairBody pair ++ [.pairEnd] := by
  rcases pair with ⟨first, second⟩
  simp [DelimitedBinaryWordPairs.pairTokens, pairBody,
    List.append_assoc]

private theorem pairBody_continues
    (pair : List Bool × List Bool) :
    ∀ token ∈ pairBody pair, isPairEnd token = false := by
  intro token member
  rcases pair with ⟨first, second⟩
  simp only [pairBody, List.mem_cons, List.mem_append, List.mem_map]
    at member
  rcases member with rfl | ⟨bit, _, rfl⟩ | rfl | ⟨bit, _, rfl⟩ <;>
    rfl

private theorem blocksAux_append_pairEnd
    (reverseBlock body rest : List PairToken)
    (continues : ∀ token ∈ body, isPairEnd token = false) :
    blocksAux isPairEnd reverseBlock (body ++ .pairEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.pairEnd]) ::
        blocksAux isPairEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [blocksAux, isPairEnd]
  | cons token body induction =>
      have tokenContinues : isPairEnd token = false :=
        continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isPairEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

private theorem blocksAux_pairTokens_append
    (pair : List Bool × List Bool) (rest : List PairToken) :
    blocksAux isPairEnd []
        (DelimitedBinaryWordPairs.pairTokens pair ++ rest) =
      DelimitedBinaryWordPairs.pairTokens pair ::
        blocksAux isPairEnd [] rest := by
  rw [pairTokens_eq_body, List.append_assoc]
  exact blocksAux_append_pairEnd [] (pairBody pair) rest
    (pairBody_continues pair)

@[simp] theorem blocks_encode
    (input : DelimitedBinaryWordPairs.Input) :
    blocks isPairEnd (DelimitedBinaryWordPairs.encode input) =
      input.pairs.map DelimitedBinaryWordPairs.pairTokens := by
  rcases input with ⟨pairs⟩
  unfold blocks DelimitedBinaryWordPairs.encode
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, blocksAux_pairTokens_append,
        List.map_cons, induction]

private theorem flatMap_singletons_eq_map
    {Source Target : Type} (function : Source → Target)
    (values : List Source) :
    values.flatMap (fun value => [function value]) =
      values.map function := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [induction]

@[simp] theorem componentTokens_pairTokens
    (pair : List Bool × List Bool) :
    componentTokens (DelimitedBinaryWordPairs.pairTokens pair) =
      DelimitedBinaryWords.wordTokens pair.1 ++
        DelimitedBinaryWords.wordTokens pair.2 := by
  rcases pair with ⟨first, second⟩
  simp [componentTokens, componentBlock,
    DelimitedBinaryWordPairs.pairTokens,
    DelimitedBinaryWords.wordTokens, List.flatMap_map,
    flatMap_singletons_eq_map, List.append_assoc]

@[simp] theorem duplicatedComponentTokens_pairTokens
    (pair : List Bool × List Bool) :
    duplicatedComponentTokens
        (DelimitedBinaryWordPairs.pairTokens pair) =
      (DelimitedBinaryWords.wordTokens pair.1 ++
        DelimitedBinaryWords.wordTokens pair.2) ++
      (DelimitedBinaryWords.wordTokens pair.1 ++
        DelimitedBinaryWords.wordTokens pair.2) := by
  simp [duplicatedComponentTokens]

/-- On canonical pair input, the physical block map emits exactly four
endpoint words per pair. -/
@[simp] theorem tokens_encode
    (input : DelimitedBinaryWordPairs.Input) :
    tokens (DelimitedBinaryWordPairs.encode input) =
      DelimitedBinaryWords.encode (expandedInput input) := by
  rcases input with ⟨pairs⟩
  unfold tokens mappedOutput
  rw [blocks_encode]
  unfold expandedInput DelimitedBinaryWords.encode
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [duplicatedComponentTokens_pairTokens, induction]
      simp [List.append_assoc]

end LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion
