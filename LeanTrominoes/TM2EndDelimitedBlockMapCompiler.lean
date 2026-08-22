/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapTimeBound

/-! # Polynomial-time end-delimited block-map compiler -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability StateTransition Turing

section

variable {Source Target : Type}
variable [Fintype Source] [Fintype Target]
variable [Inhabited Source] [Inhabited Target]
variable {function : List Source → List Target}

def inputAlphabetEquiv
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) :
    (machine inner isEnd).Γ (machine inner isEnd).k₀ ≃ Source :=
  Equiv.refl Source

def outputAlphabetEquiv
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) :
    (machine inner isEnd).Γ (machine inner isEnd).k₁ ≃ Target :=
  Equiv.refl Target

@[simp] theorem inputAlphabetEquiv_invFun
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (symbol : Source) :
    (inputAlphabetEquiv inner isEnd).invFun symbol = symbol := by
  rfl

@[simp] theorem map_inputAlphabetEquiv_invFun
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (symbols : List Source) :
    symbols.map (inputAlphabetEquiv inner isEnd).invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol remaining induction =>
      simp only [List.map_cons]
      rw [inputAlphabetEquiv_invFun inner isEnd]
      rw [induction]
      rfl

@[simp] theorem outputAlphabetEquiv_invFun
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (symbol : Target) :
    (outputAlphabetEquiv inner isEnd).invFun symbol = symbol := by
  rfl

@[simp] theorem map_outputAlphabetEquiv_invFun
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (symbols : List Target) :
    symbols.map (outputAlphabetEquiv inner isEnd).invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol remaining induction =>
      simp only [List.map_cons]
      rw [outputAlphabetEquiv_invFun inner isEnd]
      rw [induction]
      rfl

/-- Polynomial-time functions are closed under independently mapping them
over every complete end-delimited block. -/
def computableInPolyTime
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) :
    TM2ComputableInPolyTime id id (mappedOutput isEnd function) where
  tm := machine inner isEnd
  inputAlphabet := inputAlphabetEquiv inner isEnd
  outputAlphabet := outputAlphabetEquiv inner isEnd
  time := mapTimePolynomial inner
  outputsFun input := by
    let raw := machineRun inner isEnd input
    have exact : TM2OutputsInTime (machine inner isEnd)
        (List.map (inputAlphabetEquiv inner isEnd).invFun (id input))
        (some (List.map (outputAlphabetEquiv inner isEnd).invFun
          (id (mappedOutput isEnd function input))))
        (mapRunTime inner isEnd input [] []) := by
      change EvalsToInTime (machine inner isEnd).step
        (initList (machine inner isEnd)
          (List.map (inputAlphabetEquiv inner isEnd).invFun input))
        (some (haltList (machine inner isEnd)
          (List.map (outputAlphabetEquiv inner isEnd).invFun
            (mappedOutput isEnd function input))))
        (mapRunTime inner isEnd input [] [])
      rw [map_inputAlphabetEquiv_invFun,
        map_outputAlphabetEquiv_invFun]
      exact raw
    refine
      { toEvalsTo := exact.toEvalsTo
        steps_le_m := ?_ }
    simpa only [id_eq] using exact.steps_le_m.trans
      (initialMapRunTime_le_polynomial inner isEnd input)

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
