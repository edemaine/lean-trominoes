/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EndDelimitedBlockFixedCopiesCompiler

/-! # Block semantics for fixed copies of end-delimited streams -/

namespace LeanTrominoes.EndDelimitedBlockFixedCopies

/-- Add the closing delimiter to one payload body. -/
def completeBlock {Symbol : Type} (blockEnd : Symbol)
    (body : List Symbol) : List Symbol :=
  body ++ [blockEnd]

/-- Repeating one physical block is the same as mapping that block over a
fixed-size list of copies of its semantic value. -/
theorem copiedBlock_eq_replicate_flatMap
    {Value Symbol : Type} (copies : Nat) (value : Value)
    (block : Value → List Symbol) :
    copiedBlock copies (block value) =
      (List.replicate copies value).flatMap block := by
  induction copies with
  | zero => rfl
  | succ copies induction =>
      rw [copiedBlock_succ, List.replicate_succ,
        List.flatMap_cons, induction]

private theorem blocksAux_completeBlock_append
    {Symbol : Type} (isEnd : Symbol → Bool) (blockEnd : Symbol)
    (ends : isEnd blockEnd = true)
    (reverseBlock body rest : List Symbol)
    (continues : ∀ token ∈ body, isEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (completeBlock blockEnd body ++ rest) =
      (reverseBlock.reverse ++ completeBlock blockEnd body) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  unfold completeBlock
  rw [List.append_assoc]
  induction body generalizing reverseBlock with
  | nil =>
      simp [TM2EndDelimitedBlockMap.blocksAux, ends]
  | cons token body induction =>
      have tokenContinues := continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

/-- Splitting a concatenation of explicitly framed bodies recovers exactly
the same complete blocks. -/
theorem blocks_completeBlocks
    {Symbol : Type} (isEnd : Symbol → Bool) (blockEnd : Symbol)
    (ends : isEnd blockEnd = true) (bodies : List (List Symbol))
    (continues : ∀ body ∈ bodies, ∀ token ∈ body,
      isEnd token = false) :
    TM2EndDelimitedBlockMap.blocks isEnd
        (bodies.flatMap (completeBlock blockEnd)) =
      bodies.map (completeBlock blockEnd) := by
  unfold TM2EndDelimitedBlockMap.blocks
  induction bodies with
  | nil => rfl
  | cons body bodies induction =>
      have bodyContinues : ∀ token ∈ body,
          isEnd token = false :=
        continues body (by simp)
      have remainingContinues : ∀ remaining ∈ bodies,
          ∀ token ∈ remaining, isEnd token = false := by
        intro remaining member
        exact continues remaining (by simp [member])
      rw [List.flatMap_cons,
        blocksAux_completeBlock_append isEnd blockEnd ends [] body
          (bodies.flatMap (completeBlock blockEnd)) bodyContinues,
        induction remainingContinues]
      rfl

/-- Fixed-copy mapping of explicitly framed bodies is exactly the
concatenation of the fixed copies of those complete blocks. -/
theorem copiedTokens_completeBlocks
    {Symbol : Type} (copies : Nat) (isEnd : Symbol → Bool)
    (blockEnd : Symbol) (ends : isEnd blockEnd = true)
    (bodies : List (List Symbol))
    (continues : ∀ body ∈ bodies, ∀ token ∈ body,
      isEnd token = false) :
    copiedTokens copies isEnd
        (bodies.flatMap (completeBlock blockEnd)) =
      bodies.flatMap fun body =>
        copiedBlock copies (completeBlock blockEnd body) := by
  unfold copiedTokens TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_completeBlocks isEnd blockEnd ends bodies continues,
    List.flatMap_map]

end LeanTrominoes.EndDelimitedBlockFixedCopies
