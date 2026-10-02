/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATCoverCriterion
import LeanTrominoes.PeriodicTwoSATPreparation
import LeanTrominoes.FiniteTwoSATQueries

/-! # An executable periodic 2SAT solver in every fixed dimension

Input variables are explicit dense slots. Empty clauses are rejected; units
are duplicated binary clauses. A verified finite cover replaces the infinite
implication graph, and indexed Horn worklists answer the reachability queries.
The returned Nat is a ghost indexed-RAM operation counter.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph
variable {n d : Nat}

instance periodNeZero (n d : Nat) : NeZero (period (Fin n) d) :=
  ⟨Nat.ne_of_gt (period_positive (V := Fin n) (d := d))⟩

def opposites (n d M : Nat) [NeZero M] : List (Fin (n*2*M^d) × Fin (n*2*M^d)) :=
  (List.finRange n).map (fun a =>
    (coverIndex n d M ((a,true),0),coverIndex n d M ((a,false),0)))

theorem opposites_correct (formula : Formula (Fin n) d) (M : Nat) [NeZero M] :
    (checkPairs (coverEdges formula M) (opposites n d M)).1=true ↔ ∀ a : Fin n,
      ¬ (CoverReach (arcs formula) M ((a,true),0) ((a,false),0) ∧
        CoverReach (arcs formula) M ((a,false),0) ((a,true),0)) := by
  rw [checkPairs_correct]
  simp [opposites,coverEdges_reach]

/-- A conservative charge for computing the period, including bounded integer powers. -/
def periodCharge (n d : Nat) : Nat := indexCharge d*(determinantBound (2*n) d 2+1)

def solve (formula : Formula (Fin n) d) : Bool × Nat :=
  if none ∈ formula then (false,formula.length+1)
  else
    let M := period (Fin n) d
    let compiled := compileCover formula M
    let queries := checkPairs compiled.1 (opposites n d M)
    (queries.1,formula.length+1+periodCharge n d+compiled.2+n*(indexCharge d+4)+1+queries.2+4)

/-- Correctness includes empty clauses, units, and dimension zero. -/
theorem solve_correct (formula : Formula (Fin n) d) (locality : Local formula) :
    (solve formula).1=true ↔ Satisfiable formula := by
  rw [satisfiable_iff_cover formula locality]
  unfold solve
  split_ifs with empty
  · simp [empty]
  · simp only [Prod.fst,compileCover_value,opposites_correct]
    simp [empty]

def sizeBound (formula : Formula (Fin n) d) : Nat :=
  formula.length+n+determinantBound (2*n) d 2+(arcs formula).length+(period (Fin n) d)^d+1

private theorem product3_bound (a b c W : Nat) (ha : a ≤ W) (hb : b ≤ W) (hc : c ≤ W) : a*b*c ≤ W^3 := by
  simpa [pow_succ] using Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc

/-- Complete operation bound including the cover table, query preparation, and Horn worklists. -/
theorem solve_cost_bound (formula : Formula (Fin n) d) :
    (solve formula).2 ≤ 2000*(indexCharge d+10)*(sizeBound formula)^3 := by
  let W := sizeBound formula
  let J := indexCharge d+10
  have Wpositive : 1 ≤ W := by dsimp [W,sizeBound]; omega
  have Jpositive : 1 ≤ J := by dsimp [J]; omega
  have nbound : n ≤ W := by dsimp [W,sizeBound]; omega
  have fbound : formula.length+1 ≤ W := by dsimp [W,sizeBound]; omega
  have dbound : determinantBound (2*n) d 2+1 ≤ W := by dsimp [W,sizeBound]; omega
  have ebound : (arcs formula).length+1 ≤ W := by dsimp [W,sizeBound]; omega
  have mbound : (period (Fin n) d)^d ≤ W := by dsimp [W,sizeBound]; omega
  have Jbound : indexCharge d ≤ J := by dsimp [J]; omega
  have Jbound4 : indexCharge d+4 ≤ J := by dsimp [J]; omega
  have clauseCharge : 4*d+10 ≤ J := by dsimp [J,indexCharge]; nlinarith
  have Wsquare : W ≤ W^2 := by nlinarith
  have Wcube : W ≤ W^3 := by nlinarith
  have squareCube : W^2 ≤ W^3 := by nlinarith
  have JCpositive : 1 ≤ J*W^3 := by nlinarith
  have cubeJ : W^3 ≤ J*W^3 := Nat.le_mul_of_pos_left _ (by omega)
  have squareJ : J*W^2 ≤ J*W^3 := Nat.mul_le_mul_left J squareCube
  have linearJ : J*W ≤ J*W^3 := Nat.mul_le_mul_left J Wcube
  have periodBound : periodCharge n d ≤ J*W := by
    exact Nat.mul_le_mul Jbound dbound
  have compilerBound : (compileCover formula (period (Fin n) d)).2 ≤ 4*J*W^3+2 := by
    rw [compileCover_cost]
    have clause := Nat.mul_le_mul (Nat.le_of_succ_le fbound) clauseCharge
    have records := Nat.mul_le_mul (Nat.mul_le_mul mbound ebound) Jbound4
    have reordered : (period (Fin n) d)^d*((arcs formula).length+1)*(indexCharge d+4) ≤ J*W^2 := by
      simpa [pow_two,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using records
    nlinarith
  have pairBound :
      (checkPairs (coverEdges formula (period (Fin n) d)) (opposites n d (period (Fin n) d))).2 ≤ 1525*W^3 := by
    have bound := checkPairs_cost (coverEdges formula (period (Fin n) d)) (opposites n d (period (Fin n) d))
    have pairsLength : (opposites n d (period (Fin n) d)).length=n := by simp [opposites]
    rw [pairsLength,coverEdges_length] at bound
    have first := product3_bound n n ((period (Fin n) d)^d) W nbound nbound mbound
    have second := product3_bound n (arcs formula).length ((period (Fin n) d)^d) W nbound (by omega) mbound
    nlinarith
  unfold solve
  split_ifs
  · change formula.length+1 ≤ 2000*J*W^3
    nlinarith
  · simp only [Prod.snd,compileCover_value]
    change formula.length+1+periodCharge n d+(compileCover formula (period (Fin n) d)).2+
      n*(indexCharge d+4)+1+
      (checkPairs (coverEdges formula (period (Fin n) d)) (opposites n d (period (Fin n) d))).2+4 ≤ 2000*J*W^3
    have indices := Nat.mul_le_mul nbound Jbound4
    nlinarith

end LeanTrominoes.PeriodicTwoSAT
