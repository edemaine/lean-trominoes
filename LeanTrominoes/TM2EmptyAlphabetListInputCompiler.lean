/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ConstantValueCompiler
import LeanTrominoes.TM2PolyTimeFunctionTransport

/-! # Arbitrary list-input functions over an empty alphabet -/

noncomputable section

namespace LeanTrominoes.TM2EmptyAlphabetListInputCompiler

open Computability Turing

/-- If the finite input alphabet is empty, every symbol list is empty, so any
semantic function on such lists is a fixed polynomial-time constant. -/
noncomputable def computableInPolyTime
    {InputSymbol Output OutputSymbol : Type}
    [Fintype InputSymbol] [IsEmpty InputSymbol]
    [Fintype OutputSymbol] [Inhabited OutputSymbol]
    (encodeOutput : Output → List OutputSymbol)
    (function : List InputSymbol → Output) :
    @TM2ComputableInPolyTime
      (List InputSymbol) Output InputSymbol OutputSymbol
      id encodeOutput function := by
  apply TM2PolyTimeFunctionTransport.of_output_eq
    (TM2ConstantValueCompiler.computableInPolyTime
      (Input := List InputSymbol) id encodeOutput (function []))
  intro symbols
  cases symbols with
  | nil => rfl
  | cons symbol _ => exact isEmptyElim symbol

end LeanTrominoes.TM2EmptyAlphabetListInputCompiler

end
