/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Same-input native-list forks for arbitrary finite alphabets -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Computability Turing

/-- Native-list polynomial-time functions can be run on the same input and
paired even when the input alphabet is empty. -/
noncomputable def nativeComputableInPolyTime
    {InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited FirstSymbol] [Inhabited SecondSymbol]
    {first : List InputSymbol → List FirstSymbol}
    {second : List InputSymbol → List SecondSymbol}
    (firstCompiler : TM2ComputableInPolyTime id id first)
    (secondCompiler : TM2ComputableInPolyTime id id second) :
    TM2ComputableInPolyTime id
      (SeparatedProductEncoding.encode id id)
      (fun input => (first input, second input)) := by
  classical
  apply Classical.choice
  rcases isEmpty_or_nonempty InputSymbol with empty | nonempty
  · letI : IsEmpty InputSymbol := empty
    letI : Inhabited
        (SeparatedProductEncoding.Token FirstSymbol SecondSymbol) :=
      ⟨.separator⟩
    let tagged := TM2CompositionMachine.computableInPolyTime
      firstCompiler
      (FiniteBlockTransducer.computableInPolyTime
        (fun symbol : FirstSymbol =>
          ([SeparatedProductEncoding.Token.left symbol] :
            List (SeparatedProductEncoding.Token
              FirstSymbol SecondSymbol))))
    let suffix :
        List (SeparatedProductEncoding.Token FirstSymbol SecondSymbol) :=
      .separator :: (second []).map .right
    let paired := TM2CompositionMachine.computableInPolyTime tagged
      (TM2ListAppend.appendFixedComputableInPolyTime suffix)
    exact ⟨TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun input => by
        have inputEq : input = [] := by
          cases input with
          | nil => rfl
          | cons symbol _ => exact isEmptyElim symbol
        subst input
        simp [TM2ListAppend.appendFixedWords, suffix,
          SeparatedProductEncoding.encode]
        induction first [] with
        | nil => rfl
        | cons symbol symbols induction => simp [induction])⟩
  · letI : Inhabited InputSymbol := ⟨Classical.choice nonempty⟩
    exact ⟨computableInPolyTime firstCompiler secondCompiler⟩

end TM2ForkMachine
end LeanTrominoes

end
