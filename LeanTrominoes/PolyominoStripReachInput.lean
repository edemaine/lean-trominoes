/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSavitchRun
import LeanTrominoes.PartrecFuelLinearSpace

/-! # Certified initialization of a variable-tile reachability request -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
set_option maxRecDepth 10000
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def reachRequest (bits first last : Nat) (rest : List Nat) : List Nat := [2^bits,bits,first,last] ++ rest

def reachInputUnit (bits first last : Nat) (rest : List Nat) : Nat :=
  encodedListSpace (reachRequest bits first last rest)+fuelBits bits+1

def reachFuelCode : Code := Code.divideEvalFuelCode.comp (Code.prepend (Code.get 0) (Code.get 1))

def reachFuelCoefficient : Nat := fuelLinearCoefficient+120004

def reachInputCode : Code :=
  Code.prepend reachFuelCode (Code.prepend Code.zero (Code.prepend (Code.get 0)
    (Code.prepend Code.zero (Code.prepend Code.zero (Code.prepend (Code.get 1)
      (Code.prepend (Code.get 2) (Code.prepend (Code.get 3) (Code.drop 4))))))))

def reachInputCoefficient : Nat :=
  4*(reachFuelCoefficient+4*(10000+4*(10000+4*(10000+4*(10000+
    4*(20000+4*(30000+4*(40000+50000+1)+1)+1)+1)+1)+1)+1)+1)

theorem reachFuel_eval (bits first last : Nat) (rest : List Nat) :
    reachFuelCode.eval (reachRequest bits first last rest) = pure [divideEvalFuel (2^bits) bits] := by
  simp [reachFuelCode,reachRequest]

theorem reachInput_eval (bits first last : Nat) (rest : List Nat) :
    reachInputCode.eval (reachRequest bits first last rest) = pure
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList rest 0 (2^bits) (divideEvalInitial bits first last)) := by
  have fuel := reachFuel_eval bits first last rest
  simp only [reachInputCode,Code.prepend_eval_eq,fuel]
  simp [reachRequest,GenericSavitchStep.flatProgramList,divideEvalProgramList,divideEvalInitial,
    DivideEvalState.toNatList,divideOptionBoolTag,divideStackToNatList]

theorem reachFuel_fits (bits first last : Nat) (rest : List Nat) :
    EvaluatorCodeFits reachFuelCode (reachRequest bits first last rest) [divideEvalFuel (2^bits) bits]
      (reachFuelCoefficient*reachInputUnit bits first last rest) := by
  let values := reachRequest bits first last rest
  let unit := reachInputUnit bits first last rest
  have hu : encodedListSpace values+1 ≤ unit := by simp [unit,reachInputUnit,values]
  have arguments := prepend_unit hu (get_unit 0 values unit hu) (get_unit 1 values unit hu)
  change EvaluatorCodeFits (Code.prepend (Code.get 0) (Code.get 1)) values [2^bits,bits] (120004*unit) at arguments
  have small : encodedListSpace [2^bits,bits] ≤ encodedListSpace values := by
    simp [values,reachRequest,encodedListSpace_cons,encodedListSpace_nil]
  have fuel := (EvaluatorCodeFits.divideEvalFuel [2^bits,bits]).mono (fuelCost_linear (2^bits) bits)
  have fuel' : EvaluatorCodeFits Code.divideEvalFuelCode [2^bits,bits] [divideEvalFuel (2^bits) bits]
      (fuelLinearCoefficient*unit) := by
    apply fuel.mono
    have hb := fuel_length_le bits
    apply Nat.mul_le_mul_left
    dsimp only [unit,reachInputUnit]
    change encodedListSpace [2^bits,bits] ≤ encodedListSpace (reachRequest bits first last rest) at small
    omega
  have result := comp fuel' arguments
  change EvaluatorCodeFits reachFuelCode values [divideEvalFuel (2^bits) bits]
    (fuelLinearCoefficient*unit+120004*unit) at result
  have eq : fuelLinearCoefficient*unit+120004*unit = reachFuelCoefficient*unit := by
    unfold reachFuelCoefficient
    exact (Nat.add_mul fuelLinearCoefficient 120004 unit).symm
  rw [eq] at result
  exact result

theorem reachInput_fits (bits first last : Nat) (rest : List Nat) :
    EvaluatorCodeFits reachInputCode (reachRequest bits first last rest)
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList rest 0 (2^bits) (divideEvalInitial bits first last))
      (reachInputCoefficient*reachInputUnit bits first last rest) := by
  let values := reachRequest bits first last rest
  let unit := reachInputUnit bits first last rest
  have hu : encodedListSpace values+1 ≤ unit := by simp [unit,reachInputUnit,values]
  have fuel := reachFuel_fits bits first last rest
  have result := prepend_unit hu fuel (prepend_unit hu (zero_unit values unit hu)
    (prepend_unit hu (get_unit 0 values unit hu) (prepend_unit hu (zero_unit values unit hu)
      (prepend_unit hu (zero_unit values unit hu) (prepend_unit hu (get_unit 1 values unit hu)
        (prepend_unit hu (get_unit 2 values unit hu) (prepend_unit hu (get_unit 3 values unit hu) (drop_unit 4 values unit hu))))))))
  change EvaluatorCodeFits reachInputCode values
    (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList rest 0 (2^bits) (divideEvalInitial bits first last))
    (reachInputCoefficient*unit) at result
  exact result

end LeanTrominoes.PolyominoStripWindow.Savitch
