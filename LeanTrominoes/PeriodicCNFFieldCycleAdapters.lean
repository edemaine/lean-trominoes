/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldReach

/-! # Fixed-width adapters for the two cycle-search counters -/

namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def pairValues (bits first second : Nat) (rest : List Nat) : List Nat := [second,first,2^bits,bits] ++ rest

def pairReachInputCode : Code := Code.prepend (Code.get 2) (Code.prepend (Code.get 3)
  (Code.prepend (Code.get 0) (Code.prepend (Code.get 1) (Code.drop 4))))

def pairTransitionInputCode : Code := Code.prepend (Code.get 4) (Code.prepend (Code.get 5)
  (Code.prepend (Code.get 6) (Code.prepend (Code.get 1) (Code.prepend (Code.get 0) (Code.drop 9)))))

def pairReachCoefficient : Nat := 4*(30000+4*(40000+4*(10000+4*(20000+50000+1)+1)+1)+1)
def pairTransitionCoefficient : Nat := 4*(50000+4*(60000+4*(70000+4*(20000+4*(10000+100000+1)+1)+1)+1)+1)

theorem pairReachInput_eval (bits first second : Nat) (rest : List Nat) :
    pairReachInputCode.eval (pairValues bits first second rest) = pure (reachRequest bits second first rest) := by
  simp [pairReachInputCode,pairValues,reachRequest]

theorem pairTransitionInput_eval (f : PeriodicCNF Nat) (bits first second : Nat) :
    pairTransitionInputCode.eval (pairValues bits first second (suffix f)) =
      pure (FieldPredicate.input f first second) := by
  simp [pairTransitionInputCode,pairValues,suffix,FieldPredicate.input,FieldPredicate.context]

theorem pairReachInput_fits (bits first second : Nat) (rest : List Nat) :
    EvaluatorCodeFits pairReachInputCode (pairValues bits first second rest) (reachRequest bits second first rest)
      (pairReachCoefficient*(encodedListSpace (pairValues bits first second rest)+1)) := by
  let values := pairValues bits first second rest
  have fit := prepend_linear (get_linear 2 values) (prepend_linear (get_linear 3 values)
    (prepend_linear (get_linear 0 values) (prepend_linear (get_linear 1 values) (drop_linear 4 values))))
  change EvaluatorCodeFits pairReachInputCode values (reachRequest bits second first rest)
    (pairReachCoefficient*(encodedListSpace values+1)) at fit
  exact fit

theorem pairTransitionInput_fits (f : PeriodicCNF Nat) (bits first second : Nat) :
    EvaluatorCodeFits pairTransitionInputCode (pairValues bits first second (suffix f))
      (FieldPredicate.input f first second)
      (pairTransitionCoefficient*(encodedListSpace (pairValues bits first second (suffix f))+1)) := by
  let values := pairValues bits first second (suffix f)
  have fit := prepend_linear (get_linear 4 values) (prepend_linear (get_linear 5 values)
    (prepend_linear (get_linear 6 values) (prepend_linear (get_linear 1 values)
      (prepend_linear (get_linear 0 values) (drop_linear 9 values)))))
  change EvaluatorCodeFits pairTransitionInputCode values (FieldPredicate.input f first second)
    (pairTransitionCoefficient*(encodedListSpace values+1)) at fit
  exact fit

theorem pair_space_le (bits first second : Nat) (rest : List Nat)
    (hf : first ≤ 2^bits) (hs : second ≤ 2^bits) :
    encodedListSpace (pairValues bits first second rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have power : 2^bits < 2^(bits+1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have c := FiniteState.encodeNat_length_le_of_lt_pow _ _ power
  have f := FiniteState.encodeNat_length_le_of_lt_pow _ _ (hf.trans_lt power)
  have s := FiniteState.encodeNat_length_le_of_lt_pow _ _ (hs.trans_lt power)
  have d := FiniteState.encodeNat_length_le_of_lt_pow _ _ (bits.lt_two_pow_self.trans power)
  simp [pairValues,requestBudget,encodedListSpace_cons]
  omega

end LeanTrominoes.PeriodicCNF.FieldSavitch
