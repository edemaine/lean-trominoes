/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneFieldCycleSearch
import Mathlib.Tactic.GCongr

/-! # Polynomial interpretation and monotonicity of the cycle-search budget -/

namespace LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
open PolyominoStripWindow.Savitch
open Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial

noncomputable def anyBudgetPolynomial (space bits leaf : Polynomial Nat) : Polynomial Nat :=
  1000*(10000000*(space+bits+1000*(leaf+4)+1)+4)

noncomputable def cycleBudgetPolynomial (bits space : Polynomial Nat) : Polynomial Nat :=
  let request := 4*(bits+2)+space
  let dfs := 3*(bits+2)+bits*(4*(bits+2)+5)+3+2*bits+5+space
  let fuel := (bits+1)*(bits+3)+1
  let countdown := 100000*(C 1000000000000000000000000000000*(dfs+C baseCoefficient*(dfs+1)+1)+fuel+1)
  let reach := C answerCoefficient*(dfs+1)+countdown+C reachInputCoefficient*(request+fuel+1)
  let pairBody := 1000*(request+C pairTransitionTotalCoefficient*(request+1)+(reach+C pairReachCoefficient*(request+1))+2)
  let pair := C pairGuardCoefficient*(request+1)+pairBody+10000*(request+1)+100*(request+2)
  let inner := anyBudgetPolynomial request (bits+1) pair
  let outer := inner+C (prependFieldCoefficient 1)*(request+1)
  anyBudgetPolynomial request (bits+1) outer+C (prependFieldCoefficient 0)*(request+1)

theorem cycleBudgetPolynomial_eval (bits space : Polynomial Nat) (length : Nat) :
    (cycleBudgetPolynomial bits space).eval length = cycleBudget (bits.eval length) (space.eval length) := by
  simp only [cycleBudgetPolynomial,anyBudgetPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat,cycleBudget,outerAnyBudget,outerBudget,innerAnyBudget,
    boundedAnyBudget,pairBudget,guardBudget,pairBodyBudget,reachBudget,countdownBudget,
    FiniteState.GenericSavitchReach.reachBudget,iterationBudget,stateBudget,requestBudget,fuelBits]

theorem cycleBudget_mono {bits bits' space space' : Nat} (hb : bits ≤ bits') (hs : space ≤ space') :
    cycleBudget bits space ≤ cycleBudget bits' space' := by
  unfold cycleBudget outerAnyBudget outerBudget innerAnyBudget boundedAnyBudget pairBudget guardBudget
    pairBodyBudget reachBudget countdownBudget FiniteState.GenericSavitchReach.reachBudget iterationBudget
    stateBudget requestBudget fuelBits
  gcongr

end LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
