/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Computability.TuringMachine.Computable

/-! # Extensional transport of polynomial-time TM2 certificates -/

noncomputable section

namespace Turing.TM2ComputableInPolyTime

/-- Reuse a machine certificate after pointwise identification of its
mathematical output function. -/
noncomputable def of_eq
    {Input Output InputSymbol OutputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeOutput : Output → List OutputSymbol}
    {first second : Input → Output}
    (certificate : TM2ComputableInPolyTime
      encodeInput encodeOutput first)
    (equal : ∀ input, first input = second input) :
    TM2ComputableInPolyTime encodeInput encodeOutput second :=
  { tm := certificate.tm
    inputAlphabet := certificate.inputAlphabet
    outputAlphabet := certificate.outputAlphabet
    time := certificate.time
    outputsFun := fun input => by
      rw [← equal input]
      exact certificate.outputsFun input }

end Turing.TM2ComputableInPolyTime

end
