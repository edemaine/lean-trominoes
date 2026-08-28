/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ConstantListCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time compilation from subsingleton input types -/

noncomputable section

namespace LeanTrominoes.TM2SubsingletonInputCompiler

open Computability Turing

/-- Every function on an inhabited subsingleton domain is a constant
polynomial-time computation. -/
noncomputable def computableInPolyTime
    {Input Output InputSymbol OutputSymbol : Type}
    [Subsingleton Input] [Inhabited Input]
    [Fintype InputSymbol] [Fintype OutputSymbol] [Inhabited OutputSymbol]
    (encodeInput : Input → List InputSymbol)
    (encodeOutput : Output → List OutputSymbol)
    (function : Input → Output) :
    TM2ComputableInPolyTime encodeInput encodeOutput function := by
  let physical := TM2ConstantListCompiler.computableInPolyTime encodeInput
    (encodeOutput (function default))
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical ?_
  intro input
  exact congrArg (fun source => encodeOutput (function source))
    (Subsingleton.elim default input)

end LeanTrominoes.TM2SubsingletonInputCompiler

end
