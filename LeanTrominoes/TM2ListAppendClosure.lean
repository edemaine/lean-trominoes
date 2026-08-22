/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ListAppendCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime

/-! # Polynomial-time closure under same-input list concatenation -/

noncomputable section

namespace LeanTrominoes
namespace TM2ListAppend

open Computability Turing

/-- Two polynomial-time list outputs on the same input can be concatenated
in polynomial time. -/
noncomputable def computableInPolyTime
    {Input InputSymbol OutputSymbol : Type}
    [Fintype InputSymbol] [Fintype OutputSymbol]
    [Inhabited InputSymbol] [Inhabited OutputSymbol]
    {encodeInput : Input → List InputSymbol}
    {first second : Input → List OutputSymbol}
    (firstCompiler : TM2ComputableInPolyTime encodeInput id first)
    (secondCompiler : TM2ComputableInPolyTime encodeInput id second) :
    TM2ComputableInPolyTime encodeInput id
      (fun input => first input ++ second input) := by
  let paired := TM2ForkMachine.computableInPolyTime
    firstCompiler secondCompiler
  let merged := TM2CompositionMachine.computableInPolyTime paired
    (mergeComputableInPolyTime (Symbol := OutputSymbol))
  change TM2ComputableInPolyTime encodeInput id
    (fun input => appendPair (first input, second input))
  exact merged

end TM2ListAppend
end LeanTrominoes

end
