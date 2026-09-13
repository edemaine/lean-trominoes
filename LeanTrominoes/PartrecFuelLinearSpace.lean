/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecFuelSpace

/-! # Fuel construction uses linear space in input and output binary lengths -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits

def fuelLinearCoefficient : Nat := 1000000000000000000000000000000000000000000000000000000

theorem fuelCost_linear (count depth : Nat) :
    divideEvalFuelCost [count,depth] ≤ fuelLinearCoefficient*(encodedListSpace [count,depth]+
      (Computability.encodeNat (LeanTrominoes.FiniteState.divideEvalFuel count depth)).length+1) := by
  let fuel := LeanTrominoes.FiniteState.divideEvalFuel count depth
  have countPlus : (Computability.encodeNat (count+1)).length ≤ (Computability.encodeNat count).length+1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le count
  have depthPlus : (Computability.encodeNat (depth+1)).length ≤ (Computability.encodeNat depth).length+1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le depth
  have fuelPlus : (Computability.encodeNat (fuel+1)).length ≤ (Computability.encodeNat fuel).length+1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le fuel
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  simp [divideEvalFuelCost,divideEvalFuelInputCost,fuelOuterLoopCost,fuelLinearCoefficient,
    prependCost,getCost,dropCost,idCost,headCost,nilCost,oneCost,zeroCost,zeroPrimeCost,tailCost,succCost,
    encodedListSpace_cons,encodedListSpace_nil,zeroBits,oneBits]
  change _ ≤ _ at fuelPlus
  dsimp only [fuel] at fuelPlus
  omega

end Turing.PartrecToTM2.EvaluatorCodeFits
