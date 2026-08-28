/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBlockMapSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordRoleCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Fixed-block crossover compact atom-word decoration -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open Computability Turing
open PlanarThreeSAT

/-- Concatenate the independently compiled decorations for a fixed role
list. -/
def tokensFor (roleList : List CrossoverVariable)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  roleList.flatMap fun role => roleTokens role source

noncomputable def tokensForComputableInPolyTime :
    (roleList : List CrossoverVariable) →
      TM2ComputableInPolyTime id id (tokensFor roleList)
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
      intro source
      have outputEq :
          source.flatMap (fun _ : DelimitedBinaryWords.Token =>
            ([] : List DelimitedBinaryWords.Token)) = [] := by
        induction source with
        | nil => rfl
        | cons _ source induction => exact induction
      have run := empty.outputsFun source
      rw [outputEq] at run
      exact run
  | role :: roleList => by
      change TM2ComputableInPolyTime id id
        (fun source =>
          roleTokens role source ++ tokensFor roleList source)
      exact TM2ListAppend.computableInPolyTime
        (roleTokensComputableInPolyTime role)
        (tokensForComputableInPolyTime roleList)

@[simp] theorem tokensFor_wordTokens
    (roleList : List CrossoverVariable) (guarded : List Bool) :
    tokensFor roleList (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode
        ⟨roleList.flatMap fun role => word role guarded⟩ := by
  induction roleList with
  | nil => rfl
  | cons role roleList induction =>
      change roleTokens role (DelimitedBinaryWords.wordTokens guarded) ++
          tokensFor roleList (DelimitedBinaryWords.wordTokens guarded) = _
      rw [roleTokens_wordTokens, induction]
      simp [DelimitedBinaryWords.encode, List.flatMap_append]

/-- Map the fixed 58-role expander over each independently delimited guarded
crossing key. -/
def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    DelimitedBinaryWords.isWordEnd (tokensFor roles) source

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (tokensForComputableInPolyTime roles)
    DelimitedBinaryWords.isWordEnd

@[simp] theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (compact input) := by
  unfold tokens
  rw [DelimitedBinaryWords.mappedOutput_encode]
  rcases input with ⟨guarded⟩
  unfold compact words wordsForRoles DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro guardedWord _guardedMember
  simpa only [DelimitedBinaryWords.encode] using
    tokensFor_wordTokens roles guardedWord

/-- The fixed crossover-role block expansion is polynomial-time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode compact := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => tokens (DelimitedBinaryWords.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWords.finEncoding.encode tokensComputableInPolyTime
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    tokens_encode

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing

end
