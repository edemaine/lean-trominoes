/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ListAppendData
import LeanTrominoes.FiniteBlockTransducer

/-! # Polynomial-time separated-list concatenation -/

noncomputable section

namespace LeanTrominoes
namespace TM2ListAppend

open Computability Turing

/-- Removing the pair separator and both side tags concatenates the two
encoded list outputs in linear time. -/
noncomputable def mergeComputableInPolyTime
    {Symbol : Type} [Fintype Symbol] [Inhabited Symbol] :
    @TM2ComputableInPolyTime
      (List Symbol × List Symbol) (List Symbol)
      (PairSymbol Symbol) Symbol
      (SeparatedProductEncoding.encode id id) id appendPair := by
  let compiler := FiniteBlockTransducer.computableInPolyTime
    (mergeBlock : PairSymbol Symbol → List Symbol)
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  rintro ⟨first, second⟩
  rw [← merge_separated first second]
  exact compiler.outputsFun
    (SeparatedProductEncoding.encode id id (first, second))

end TM2ListAppend
end LeanTrominoes

end
