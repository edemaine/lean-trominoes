/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetPolyTime

/-! # Regression checks for finite-alphabet polynomial-time certificates -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetPolyTimeExamples

open Turing Complexity TM2FiniteAlphabetRestriction

/-- Input and output share one Boolean stack. The other stack has an infinite
ambient alphabet, but the program only writes 42 and then removes it. -/
abbrev ambientNatMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ := fun | false => Bool | true => Nat
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push true (fun _ => 42) (.pop true (fun _ _ => ()) .halt)

example : Allowed ambientNatMachine true 42 := by
  simp [Allowed, programSymbols, writtenSymbols, ambientNatMachine]

example : ¬ Allowed ambientNatMachine true 43 := by
  simp [Allowed, programSymbols, writtenSymbols, ambientNatMachine]

def ambientNatIdentity : TM2ComputableInPolyTime id id (id : List Bool → List Bool) where
  tm := ambientNatMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := by
    refine ⟨⟨1, ?_⟩, by simp⟩
    simp [flip, ambientNatMachine, FinTM2.step, TM2.step,
      TM2.stepAux, initList, haltList]
    rfl

example : FiniteAlphabetComputableInPolyTime id id (id : List Bool → List Bool) :=
  FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime ambientNatIdentity

/-- Restricting alphabets adds no steps to the time polynomial. -/
example :
    (FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime ambientNatIdentity).time = 1 := rfl

/-- Empty external alphabets require no default symbol or nonemptiness assumption. -/
example : FiniteAlphabetComputableInPolyTime id id (id : List Empty → List Empty) :=
  FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (idComputableInPolyTime (id : List Empty → List Empty))

end LeanTrominoes.FiniteAlphabetPolyTimeExamples

end
