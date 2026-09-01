/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Fixed copies of arbitrary end-delimited blocks -/

noncomputable section

namespace LeanTrominoes.EndDelimitedBlockFixedCopies

open Computability Turing

/-- Repeat one complete physical block a fixed number of times. -/
def copiedBlock {Symbol : Type} : Nat → List Symbol → List Symbol
  | 0, _ => []
  | copies + 1, block => block ++ copiedBlock copies block

/-- Split at every end marker and repeat each complete block.  As with the
underlying block mapper, an unterminated suffix is ignored. -/
def copiedTokens {Symbol : Type}
    (copies : Nat) (isEnd : Symbol → Bool)
    (source : List Symbol) : List Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd
    (copiedBlock copies) source

@[simp] theorem copiedBlock_zero {Symbol : Type}
    (block : List Symbol) :
    copiedBlock 0 block = [] :=
  rfl

@[simp] theorem copiedBlock_succ {Symbol : Type}
    (copies : Nat) (block : List Symbol) :
    copiedBlock (copies + 1) block = block ++ copiedBlock copies block :=
  rfl

@[simp] theorem copiedBlock_length {Symbol : Type}
    (copies : Nat) (block : List Symbol) :
    (copiedBlock copies block).length = copies * block.length := by
  induction copies with
  | zero => simp [copiedBlock]
  | succ copies induction =>
      rw [copiedBlock_succ, List.length_append, induction]
      rw [Nat.add_mul]
      omega

/-- Fixed repetition of one native block is polynomial-time computable. -/
noncomputable def copiedBlockComputableInPolyTime
    {Symbol : Type} [Fintype Symbol] [Inhabited Symbol] :
    (copies : Nat) →
      TM2ComputableInPolyTime id id
        (copiedBlock (Symbol := Symbol) copies)
  | 0 => by
      change TM2ComputableInPolyTime id id
        (fun _ : List Symbol => [])
      let empty := FiniteBlockTransducer.computableInPolyTime
        (fun _ : Symbol => ([] : List Symbol))
      refine
        { tm := empty.tm
          inputAlphabet := empty.inputAlphabet
          outputAlphabet := empty.outputAlphabet
          time := empty.time
          outputsFun := ?_ }
      intro source
      have outputEq :
          source.flatMap (fun _ : Symbol => ([] : List Symbol)) = [] := by
        induction source with
        | nil => rfl
        | cons symbol source induction => exact induction
      have run := empty.outputsFun source
      rw [outputEq] at run
      exact run
  | copies + 1 => by
      change TM2ComputableInPolyTime id id
        (fun block : List Symbol =>
          block ++ copiedBlock copies block)
      exact TM2ListAppend.computableInPolyTime
        RetainedInputAppendPipeline.identityComputableInPolyTime
        (copiedBlockComputableInPolyTime copies)

/-- Repeating every complete end-delimited block a fixed number of times is
polynomial-time computable. -/
noncomputable def computableInPolyTime
    {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (copies : Nat) (isEnd : Symbol → Bool) :
    TM2ComputableInPolyTime id id
      (copiedTokens copies isEnd) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (copiedBlockComputableInPolyTime copies) isEnd

end LeanTrominoes.EndDelimitedBlockFixedCopies

end
