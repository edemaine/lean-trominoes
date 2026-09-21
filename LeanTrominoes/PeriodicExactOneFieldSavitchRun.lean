/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneFieldSavitchLeaf

/-! # Space bounds for the complete CNF Savitch countdown -/

namespace LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def countdownBudget (bits suffixSpace : Nat) : Nat :=
  GenericSavitchReach.reachBudget (stateBudget bits suffixSpace)
    (baseCoefficient*(stateBudget bits suffixSpace+1)) (fuelBits bits)

theorem countdown_fits (f : PeriodicCNF Nat) (bits first last : Nat)
    (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits (Code.flatIterate (DivideEvalPartrec.stepCode baseCode))
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (divideEvalInitial bits first last))
      (GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (((divideEvalStep (2^bits) (ExactOneFieldPredicate.check f))^[divideEvalFuel (2^bits) bits])
          (divideEvalInitial bits first last)))
      (countdownBudget bits (encodedListSpace (suffix f))) := by
  apply GenericSavitchReach.iterate_fits (suffix f) baseCode (ExactOneFieldPredicate.check f)
    (baseCost f) (base_fits f) 0 (2^bits)
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
    (stateBudget bits (encodedListSpace (suffix f)))
    (baseCoefficient*(stateBudget bits (encodedListSpace (suffix f))+1)) (fuelBits bits)
    (fuel_length_le bits)
  · intro taken ht
    exact state_space_le _ _ bits first last taken hf hl
  · intro taken ht
    have h := state_space_le (suffix f) (ExactOneFieldPredicate.check f) bits first last taken hf hl
    exact Nat.mul_le_mul_left baseCoefficient (Nat.add_le_add_right h 1)

end LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
