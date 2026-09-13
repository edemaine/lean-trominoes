/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSavitchLeaf

/-! # Space bounds for the complete variable-tile Savitch countdown -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def stateBudget (bits suffixSpace : Nat) : Nat :=
  3*(bits+2)+bits*(4*(bits+2)+5)+3+2*bits+5+suffixSpace

def fuelBits (bits : Nat) : Nat := (bits+1)*(bits+3)+1

theorem fuel_length_le (bits : Nat) :
    (Computability.encodeNat (divideEvalFuel (2^bits) bits)).length ≤ fuelBits bits := by
  apply FiniteState.encodeNat_length_le_of_lt_pow
  exact divideEvalFuel_lt_pow_succ (2^bits) bits bits le_rfl

theorem state_space_le (rest : List Nat) (relation : Nat → Nat → Bool) (bits first last taken : Nat)
    (hf : first < 2^bits) (hl : last < 2^bits) :
    encodedListSpace (GenericSavitchStep.flatProgramList rest 0 (2^bits)
      (((divideEvalStep (2^bits) relation)^[taken]) (divideEvalInitial bits first last))) ≤
      stateBudget bits (encodedListSpace rest) := by
  let state := ((divideEvalStep (2^bits) relation)^[taken]) (divideEvalInitial bits first last)
  have depthBound : bits < 2^(bits+1) := bits.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have stateBound := divideEvalIterate_encodedListSpace_le (2^bits) bits (bits+1) first last taken relation hf hl
    (Nat.pow_le_pow_right (by omega) (by omega)) depthBound
  have countBound : (Computability.encodeNat (2^bits)).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (Nat.pow_lt_pow_right (by omega) (by omega))
  have stackLength : state.stack.length ≤ bits :=
    divideEvalIterate_stack_length_le_depth (2^bits) bits first last taken relation
  have stackBound : (Computability.encodeNat state.stack.length).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (stackLength.trans_lt depthBound)
  change encodedListSpace ((0 :: 2^bits :: state.stack.length :: state.toNatList) ++ rest) ≤ _
  rw [encodedListSpace_append]
  simp only [encodedListSpace_cons,stateBudget]
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  rw [zeroBits]
  change encodedListSpace state.toNatList ≤ _ at stateBound
  nlinarith

def countdownBudget (bits suffixSpace : Nat) : Nat :=
  GenericSavitchReach.reachBudget (stateBudget bits suffixSpace)
    (baseCoefficient*(stateBudget bits suffixSpace+1)) (fuelBits bits)

theorem countdown_fits (cells : Bool → List Cell) (height bound bits first last : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits (Code.flatIterate (DivideEvalPartrec.stepCode baseCode))
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList (suffix cells height bound) 0 (2^bits)
        (divideEvalInitial bits first last))
      (GenericSavitchStep.flatProgramList (suffix cells height bound) 0 (2^bits)
        (((divideEvalStep (2^bits) (Raw.check cells height bound))^[divideEvalFuel (2^bits) bits])
          (divideEvalInitial bits first last)))
      (countdownBudget bits (encodedListSpace (suffix cells height bound))) := by
  apply GenericSavitchReach.iterate_fits (suffix cells height bound) baseCode (Raw.check cells height bound)
    (baseCost cells height bound) (base_fits cells height bound bounded) 0 (2^bits)
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
    (stateBudget bits (encodedListSpace (suffix cells height bound)))
    (baseCoefficient*(stateBudget bits (encodedListSpace (suffix cells height bound))+1)) (fuelBits bits)
    (fuel_length_le bits)
  · intro taken ht
    exact state_space_le _ _ bits first last taken hf hl
  · intro taken ht
    have h := state_space_le (suffix cells height bound) (Raw.check cells height bound) bits first last taken hf hl
    exact Nat.mul_le_mul_left baseCoefficient (Nat.add_le_add_right h 1)

end LeanTrominoes.PolyominoStripWindow.Savitch
