/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Fixed copies of unary fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldFixedCopies

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Repeat every semantic unary value a fixed number of times. -/
def values (copies : Nat) (source : List Nat) : List Nat :=
  source.flatMap fun value => List.replicate copies value

/-- Repeat one complete physical unary-field block. -/
def copiedBlock : Nat → List Symbol → List Symbol
  | 0, _ => []
  | copies + 1, block => block ++ copiedBlock copies block

def isFieldEnd : Symbol → Bool
  | .unit => false
  | .delimiter => true

/-- Split a unary stream at its delimiters and copy every complete field. -/
def copiedTokens (copies : Nat) (source : List Symbol) : List Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput isFieldEnd
    (copiedBlock copies) source

private theorem blocksAux_append_fieldEnd
    (reverseBlock body rest : List Symbol)
    (continues : ∀ symbol ∈ body, isFieldEnd symbol = false) :
    TM2EndDelimitedBlockMap.blocksAux isFieldEnd reverseBlock
        (body ++ .delimiter :: rest) =
      (reverseBlock.reverse ++ body ++ [.delimiter]) ::
        TM2EndDelimitedBlockMap.blocksAux isFieldEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux, isFieldEnd]
  | cons symbol body induction =>
      have symbolContinues := continues symbol (by simp)
      have bodyContinues : ∀ other ∈ body,
          isFieldEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [symbolContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (symbol :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

private theorem blocksAux_unaryField_append
    (reverseBlock : List Symbol) (value : Nat) (rest : List Symbol) :
    TM2EndDelimitedBlockMap.blocksAux isFieldEnd reverseBlock
        (UnaryFieldEncoderMachine.unaryField value ++ rest) =
      (reverseBlock.reverse ++
          UnaryFieldEncoderMachine.unaryField value) ::
        TM2EndDelimitedBlockMap.blocksAux isFieldEnd [] rest := by
  unfold UnaryFieldEncoderMachine.unaryField
  rw [List.append_assoc]
  simpa [List.append_assoc] using
    blocksAux_append_fieldEnd reverseBlock
      (List.replicate value UnaryFieldEncoderMachine.Symbol.unit) rest (by
        intro symbol member
        have symbolEq := List.eq_of_mem_replicate member
        subst symbol
        rfl)

@[simp] theorem blocks_unaryFields (source : List Nat) :
    TM2EndDelimitedBlockMap.blocks isFieldEnd
        (UnaryFieldEncoderMachine.unaryFields source) =
      source.map UnaryFieldEncoderMachine.unaryField := by
  unfold TM2EndDelimitedBlockMap.blocks
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        blocksAux_unaryField_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      exact congrArg
        (List.cons (UnaryFieldEncoderMachine.unaryField value)) induction

@[simp] theorem copiedBlock_unaryField (copies value : Nat) :
    copiedBlock copies (UnaryFieldEncoderMachine.unaryField value) =
      UnaryFieldEncoderMachine.unaryFields
        (List.replicate copies value) := by
  induction copies with
  | zero => rfl
  | succ copies induction =>
      rw [copiedBlock, List.replicate_succ,
        UnaryFieldEncoderMachine.unaryFields_cons, induction]

@[simp] theorem copiedTokens_unaryFields
    (copies : Nat) (source : List Nat) :
    copiedTokens copies (UnaryFieldEncoderMachine.unaryFields source) =
      UnaryFieldEncoderMachine.unaryFields (values copies source) := by
  unfold copiedTokens TM2EndDelimitedBlockMap.mappedOutput values
  rw [blocks_unaryFields, List.flatMap_map]
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [List.flatMap_cons, copiedBlock_unaryField, induction,
        List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append]

private noncomputable def copiedBlockComputableInPolyTime :
    (copies : Nat) → TM2ComputableInPolyTime id id (copiedBlock copies)
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
        (fun block : List Symbol => block ++ copiedBlock copies block)
      exact TM2ListAppend.computableInPolyTime
        RetainedInputAppendPipeline.identityComputableInPolyTime
        (copiedBlockComputableInPolyTime copies)

private noncomputable def copiedTokensComputableInPolyTime
    (copies : Nat) :
    TM2ComputableInPolyTime id id (copiedTokens copies) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (copiedBlockComputableInPolyTime copies) isFieldEnd

/-- Repeating every unary field a fixed number of times is polynomial-time
computable. -/
noncomputable def computableInPolyTime (copies : Nat) :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields
      (values copies) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (copiedTokensComputableInPolyTime copies)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (copiedTokens_unaryFields copies)

end LeanTrominoes.UnaryFieldFixedCopies

end
