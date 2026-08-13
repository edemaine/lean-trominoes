/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFuel

/-!
# Explicit partial-recursive powers of two

The padded strip-frontier graph uses `2 ^ depth` states.  This module computes
that bound by a flat countdown whose singleton payload doubles on every step.
Doubling reuses the explicit, tail-style addition loop from `PartrecFuel`.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Normalize a singleton value into the three-field input that adds the
value to itself. -/
def powerDoubleInputCode : Code :=
  prepend zero <|
    prepend head head

@[simp]
theorem powerDoubleInputCode_eval (values : List Nat) :
    powerDoubleInputCode.eval values =
      pure [0, values.headI, values.headI] := by
  simp [powerDoubleInputCode]

/-- Double the head natural and return it as a singleton. -/
def powerDoubleCode : Code :=
  (get 2).comp <|
    fuelAddPreviousCode.comp powerDoubleInputCode

def powerDoubleList (values : List Nat) : List Nat :=
  [2 * values.headI]

@[simp]
theorem powerDoubleCode_eval (values : List Nat) :
    powerDoubleCode.eval values =
      pure (powerDoubleList values) := by
  simp [powerDoubleCode, powerDoubleList]
  omega

theorem powerDoubleList_iterate (steps initial : Nat) :
    ((powerDoubleList)^[steps]) [initial] =
      [2 ^ steps * initial] := by
  induction steps with
  | zero =>
      simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, powerDoubleList, pow_succ]
      ring

/-- Assemble the flat doubling countdown with initial value one. -/
def powerTwoInputCode : Code :=
  prepend head one

@[simp]
theorem powerTwoInputCode_eval (values : List Nat) :
    powerTwoInputCode.eval values =
      pure [values.headI, 1] := by
  simp [powerTwoInputCode]

/-- Unary explicit code for `depth ↦ 2 ^ depth`. -/
def powerTwoCode : Code :=
  (flatIterate powerDoubleCode).comp powerTwoInputCode

@[simp]
theorem powerTwoCode_eval (depth : Nat) :
    powerTwoCode.eval [depth] =
      pure [2 ^ depth] := by
  simp [powerTwoCode, flatIterate_eval,
    powerDoubleList_iterate]

end Turing.ToPartrec.Code
