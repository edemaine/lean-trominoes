/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecBinaryLength

/-!
# Explicit quotient-and-parity decoding

Mathlib's integer encoding uses the low bit as a sign tag.  The binary
division loop already computes both the quotient and that bit; this module
exposes its full two-field result instead of projecting only the quotient.
-/

namespace Turing.ToPartrec.Code

/-- Unary code returning `[number / 2, number % 2]`. -/
def div2ParityCode : Code :=
  (flatIterate binaryDiv2ListStepCode).comp
    binaryDiv2InputCode

@[simp]
theorem div2ParityCode_eval (number : Nat) :
    div2ParityCode.eval [number] =
      pure [number.div2, number.bodd.toNat] := by
  simp [div2ParityCode,
    flatIterate_eval binaryDiv2ListStepCode
      binaryDiv2ListStep,
    binaryDiv2ListStep_iterate]

end Turing.ToPartrec.Code
