/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Same-input list concatenation for arbitrary finite alphabets -/

noncomputable section

namespace LeanTrominoes
namespace TM2ListAppend

open Computability Turing

/-- Native-list polynomial-time functions are closed under concatenation even
when the input alphabet is empty. -/
noncomputable def nativeComputableInPolyTime
    {InputSymbol OutputSymbol : Type}
    [Fintype InputSymbol] [Fintype OutputSymbol]
    [Inhabited OutputSymbol]
    {first second : List InputSymbol → List OutputSymbol}
    (firstCompiler : TM2ComputableInPolyTime id id first)
    (secondCompiler : TM2ComputableInPolyTime id id second) :
    TM2ComputableInPolyTime id id
      (fun input => first input ++ second input) := by
  classical
  apply Classical.choice
  rcases isEmpty_or_nonempty InputSymbol with empty | nonempty
  · letI : IsEmpty InputSymbol := empty
    let appended := TM2CompositionMachine.computableInPolyTime
      firstCompiler (appendFixedComputableInPolyTime (second []))
    exact ⟨TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
      (fun input => by
          have inputEq : input = [] := by
            cases input with
            | nil => rfl
            | cons symbol _ => exact isEmptyElim symbol
          subst input
          rfl)⟩
  · letI : Inhabited InputSymbol := ⟨Classical.choice nonempty⟩
    exact ⟨computableInPolyTime firstCompiler secondCompiler⟩

end TM2ListAppend
end LeanTrominoes

end
