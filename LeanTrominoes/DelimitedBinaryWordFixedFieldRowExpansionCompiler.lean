/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for fixed-field delimited-row expansion -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordFixedFieldRowExpansion

open Computability Turing

noncomputable def rowTokensComputableInPolyTime
    (width index : Nat) :
    TM2ComputableInPolyTime id id (rowTokens width index) := by
  unfold rowTokens
  exact FiniteBlockTransducer.computableInPolyTime (tokenBlock width index)

noncomputable def rowCopiesForComputableInPolyTime (width : Nat) :
    (indices : List Nat) →
      TM2ComputableInPolyTime id id (rowCopiesFor width indices)
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
  | index :: indices => by
      change TM2ComputableInPolyTime id id
        (fun source =>
          rowTokens width index source ++
            rowCopiesFor width indices source)
      exact TM2ListAppend.computableInPolyTime
        (rowTokensComputableInPolyTime width index)
        (rowCopiesForComputableInPolyTime width indices)

noncomputable def rowCopiesComputableInPolyTime (width : Nat) :
    TM2ComputableInPolyTime id id (rowCopies width) := by
  unfold rowCopies
  exact rowCopiesForComputableInPolyTime width (List.range width)

noncomputable def tokensComputableInPolyTime (width : Nat) :
    TM2ComputableInPolyTime id id (tokens width) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (rowCopiesComputableInPolyTime width)
    DelimitedBinaryWords.isWordEnd

end DelimitedBinaryWordFixedFieldRowExpansion
end LeanTrominoes

end
