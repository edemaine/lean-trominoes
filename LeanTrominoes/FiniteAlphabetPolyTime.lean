/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2FiniteAlphabetRestriction

/-! # Polynomial-time certificates with finite alphabets on every stack -/

noncomputable section

namespace LeanTrominoes.Complexity

open Turing

/-- A polynomial-time machine whose internal and external stack alphabets
are all finite. This makes the finite-alphabet requirement explicit in
complexity-class reductions. -/
structure FiniteAlphabetComputableInPolyTime
    {Input Output InputSymbol OutputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (encodeOutput : Output → List OutputSymbol) (function : Input → Output)
    extends TM2ComputableInPolyTime encodeInput encodeOutput function where
  stackAlphabetFinite : ∀ stack, Fintype (tm.Γ stack)

namespace FiniteAlphabetComputableInPolyTime

/-- Convert a Mathlib certificate to an explicitly finite-alphabet machine.
The external encodings and time polynomial are unchanged. -/
def ofComputableInPolyTime
    {Input Output InputSymbol OutputSymbol : Type} [Finite OutputSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeOutput : Output → List OutputSymbol} {function : Input → Output}
    (certificate : TM2ComputableInPolyTime encodeInput encodeOutput function) :
    FiniteAlphabetComputableInPolyTime encodeInput encodeOutput function := by
  letI : Finite (certificate.tm.Γ certificate.tm.k₁) :=
    Finite.of_equiv OutputSymbol certificate.outputAlphabet.symm
  refine
    { tm := TM2FiniteAlphabetRestriction.machine certificate.tm
      inputAlphabet :=
        (TM2FiniteAlphabetRestriction.externalEquiv certificate.tm
          certificate.tm.k₀ (Or.inl rfl)).trans certificate.inputAlphabet
      outputAlphabet :=
        (TM2FiniteAlphabetRestriction.externalEquiv certificate.tm
          certificate.tm.k₁ (Or.inr rfl)).trans certificate.outputAlphabet
      time := certificate.time
      stackAlphabetFinite := fun stack => Fintype.ofFinite _
      outputsFun := ?_ }
  intro input
  have run := TM2FiniteAlphabetRestriction.outputsInTime certificate.tm
    _ _ _ (certificate.outputsFun input)
  simpa only [List.map_map, Equiv.trans, Equiv.symm, Equiv.coe_fn_mk, Function.comp_def] using run

end FiniteAlphabetComputableInPolyTime

end LeanTrominoes.Complexity

end
