/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATEdgeEvaluation
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATMarkerTables

/-! # Agreement of arithmetic Horn cells with the dense batch tables -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open PeriodicLatticeGraph ImplicationGraph ImplicationGraph.TwoSATExpression
variable {d : ℕ}

def edgeList (raw : Raw.Input d) (M : ℕ) [NeZero M] :=
  paddedCoverEdges (by omega) (liftFormula raw.2) M

theorem edgeList_length (raw : Raw.Input d) (M : ℕ) [NeZero M] :
    (edgeList raw M).length=M^d*(raw.2.length*2) := by
  simp [edgeList,paddedCoverEdges_length,liftFormula]
  ring

structure Metadata (raw : Raw.Input d) (M : ℕ) (env : Fin 17 → ℤ) : Prop where
  numVars : env 6 = raw.1
  clauses : env 7 = raw.2.length
  period : env 8 = M
  coordinates : env 9 = M^d
  vertices : env 10 = (raw.1+1)*2*M^d
  edges : env 11 = M^d*(raw.2.length*2)
  atoms : env 12 = raw.1*2*((raw.1+1)*2*M^d)+1
  rules : env 13 = 3*raw.1+2*raw.1*(M^d*(raw.2.length*2))+raw.2.length
  occurrences : env 14 = 2*raw.1+2*raw.1*(M^d*(raw.2.length*2))
  length : env 2 = 4+(3*raw.1+2*raw.1*(M^d*(raw.2.length*2))+raw.2.length)+
    2*(2*raw.1+2*raw.1*(M^d*(raw.2.length*2)))

theorem select_eval (a b yes no : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (lengthPositive : 0 < env 2) (aNonnegative : 0 ≤ a.eval env memory)
    (aBound : a.eval env memory ≤ env 2) (bNonnegative : 0 ≤ b.eval env memory)
    (bBound : b.eval env memory ≤ env 2) :
    (select a b yes no).eval env memory =
      if a.eval env memory < b.eval env memory then yes.eval env memory else no.eval env memory := by
  exact Expr.selectLt_eval _ _ _ _ _ env memory
    (by simp only [increment,add_eval,input_eval,constant_eval]; omega)
    aNonnegative (by simp only [increment,add_eval,input_eval,constant_eval]; omega)
    bNonnegative (by simp only [increment,add_eval,input_eval,constant_eval]; omega)

theorem sourceVertex_lookup (raw : Raw.Input d) (sourceBase : ℕ) (M : ℕ) [NeZero M]
    (env : Fin 17 → ℤ) (memory : ℕ → ℤ) (source : Raw.SourceAt raw sourceBase memory)
    (baseValue : env 5 = sourceBase) (header : Metadata raw M env) (e : Expression)
    (i : Fin (edgeList raw M).length) (edgeValue : e.eval env memory = i.val) :
    (sourceVertex d e).eval env memory = ((edgeList raw M).get i).1.val := by
  let i' : Fin (M^d*(raw.2.length*2)) := ⟨i.val,by simpa [edgeList_length] using i.isLt⟩
  have lookup := paddedCoverEdges_lookup (by omega) (liftFormula raw.2)
    (M:=M) (⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩)
  have value := sourceVertex_active raw sourceBase env memory source baseValue header.clauses header.period header.coordinates e i' edgeValue
  have get : (edgeList raw M).get i = paddedEdgeAt (by omega) (liftFormula raw.2) M
      ⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩ := by
    apply Option.some.inj
    have lookup' : (edgeList raw M)[i.val]? = some (paddedEdgeAt (by omega) (liftFormula raw.2) M
        ⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩) := lookup
    rw [List.getElem?_eq_getElem i.isLt] at lookup'
    simpa only [List.get_eq_getElem] using lookup'
  rw [get]
  exact value

theorem targetVertex_lookup (raw : Raw.Input d) (sourceBase : ℕ) (M : ℕ) [NeZero M]
    (env : Fin 17 → ℤ) (memory : ℕ → ℤ) (source : Raw.SourceAt raw sourceBase memory)
    (baseValue : env 5 = sourceBase) (header : Metadata raw M env) (e : Expression)
    (i : Fin (edgeList raw M).length) (edgeValue : e.eval env memory = i.val) :
    (targetVertex d e).eval env memory = ((edgeList raw M).get i).2.val := by
  let i' : Fin (M^d*(raw.2.length*2)) := ⟨i.val,by simpa [edgeList_length] using i.isLt⟩
  have lookup := paddedCoverEdges_lookup (by omega) (liftFormula raw.2)
    (M:=M) (⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩)
  have value := targetVertex_active raw sourceBase env memory source baseValue header.clauses header.period header.coordinates e i' edgeValue
  have get : (edgeList raw M).get i = paddedEdgeAt (by omega) (liftFormula raw.2) M
      ⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩ := by
    apply Option.some.inj
    have lookup' : (edgeList raw M)[i.val]? = some (paddedEdgeAt (by omega) (liftFormula raw.2) M
        ⟨i.val,by simpa only [liftFormula,List.length_map] using (show i.val < M^d*(raw.2.length*2) from i'.isLt)⟩) := lookup
    rw [List.getElem?_eq_getElem i.isLt] at lookup'
    simpa only [List.get_eq_getElem] using lookup'
  rw [get]
  exact value

theorem sourceFact_eval (raw : Raw.Input d) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw (PeriodicTwoSAT.period (Fin (raw.1+1)) d) env) (i : Fin (raw.1*2))
    (e : Expression) (value : e.eval env memory = i.val) :
    (sourceFact e).eval env memory =
      ((TwoSATBatch.factHeads (liftedPairs raw.1 d))[i.val]?.getD 0 : ℕ) := by
  simp only [TwoSATBatch.factHeads,List.getElem?_ofFn,i.isLt,reduceDIte,Option.getD_some]
  simp only [sourceFact,increment,two,complement,direction,add_eval,mul_eval,sub_eval,div_eval,
    mod_eval,input_eval,constant_eval,value,header.vertices,header.coordinates]
  simp only [liftedPairs,coverIndex_value,Fin.val_castSucc,Pi.zero_apply,ZMod.val_zero,
    Nat.zero_mul,Finset.sum_const_zero,Nat.add_zero]
  push_cast
  rw [show (i.val : ℤ)%2 = ((i.val%2 : ℕ) : ℤ) by norm_cast]
  have rem : i.val%2 = 0 ∨ i.val%2 = 1 := by omega
  rcases rem with rem | rem <;> norm_num [rem] <;> ring

theorem oppositeTarget_eval (raw : Raw.Input d) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw (PeriodicTwoSAT.period (Fin (raw.1+1)) d) env) (i : Fin (raw.1*2))
    (e : Expression) (value : e.eval env memory = i.val) :
    (oppositeTarget e).eval env memory =
      ((TwoSATBatch.negativeAtoms (liftedPairs raw.1 d))[i.val]?.getD 0 : ℕ) := by
  simp only [TwoSATBatch.negativeAtoms,List.getElem?_ofFn,i.isLt,reduceDIte,Option.getD_some]
  simp only [oppositeTarget,increment,two,direction,add_eval,mul_eval,div_eval,
    mod_eval,input_eval,constant_eval,value,header.vertices,header.coordinates]
  simp only [liftedPairs,coverIndex_value,Fin.val_castSucc,Pi.zero_apply,ZMod.val_zero,
    Nat.zero_mul,Finset.sum_const_zero,Nat.add_zero]
  push_cast
  rw [show (i.val : ℤ)%2 = ((i.val%2 : ℕ) : ℤ) by norm_cast]
  have rem : i.val%2 = 0 ∨ i.val%2 = 1 := by omega
  rcases rem with rem | rem <;> norm_num [rem] <;> ring

theorem unaryHead_eval (raw : Raw.Input d) (sourceBase : ℕ) (M : ℕ) [NeZero M]
    (env : Fin 17 → ℤ) (memory : ℕ → ℤ) (source : Raw.SourceAt raw sourceBase memory)
    (baseValue : env 5 = sourceBase) (header : Metadata raw M env)
    (i : Fin ((raw.1*2)*(edgeList raw M).length)) (e : Expression)
    (value : e.eval env memory = i.val) :
    (unaryHead d e).eval env memory =
      ((TwoSATBatch.edgeHeads (p:=raw.1) (edgeList raw M))[i.val]?.getD 0 : ℕ) := by
  have positive : 0 < (edgeList raw M).length := by have bound := i.isLt; nlinarith
  let index : Fin (edgeList raw M).length := ⟨i.val%(edgeList raw M).length,Nat.mod_lt _ positive⟩
  have edgeValue : (mod e edges).eval env memory = index.val := by
    simp only [mod_eval,input_eval,header.edges,value,index,edgeList_length]
    norm_cast
  have target := targetVertex_lookup raw sourceBase M env memory source baseValue header (mod e edges) index edgeValue
  simp only [TwoSATBatch.edgeHeads,List.getElem?_ofFn,i.isLt,reduceDIte,Option.getD_some]
  simp only [unaryHead,increment,add_eval,mul_eval,div_eval,input_eval,value,target,header.vertices,header.edges]
  simp only [index,edgeList_length,constant_eval]
  push_cast
  rfl

theorem unaryAtom_eval (raw : Raw.Input d) (sourceBase : ℕ) (M : ℕ) [NeZero M]
    (env : Fin 17 → ℤ) (memory : ℕ → ℤ) (source : Raw.SourceAt raw sourceBase memory)
    (baseValue : env 5 = sourceBase) (header : Metadata raw M env)
    (i : Fin ((raw.1*2)*(edgeList raw M).length)) (e : Expression)
    (value : e.eval env memory = i.val) :
    (unaryAtom d e).eval env memory =
      ((TwoSATBatch.edgeAtoms (p:=raw.1) (edgeList raw M))[i.val]?.getD 0 : ℕ) := by
  have positive : 0 < (edgeList raw M).length := by have bound := i.isLt; nlinarith
  let index : Fin (edgeList raw M).length := ⟨i.val%(edgeList raw M).length,Nat.mod_lt _ positive⟩
  have edgeValue : (mod e edges).eval env memory = index.val := by
    simp only [mod_eval,input_eval,header.edges,value,index,edgeList_length]
    norm_cast
  have sourceValue := sourceVertex_lookup raw sourceBase M env memory source baseValue header (mod e edges) index edgeValue
  simp only [TwoSATBatch.edgeAtoms,List.getElem?_ofFn,i.isLt,reduceDIte,Option.getD_some]
  simp only [unaryAtom,increment,add_eval,mul_eval,div_eval,input_eval,value,sourceValue,header.vertices,header.edges]
  simp only [index,edgeList_length,constant_eval]
  push_cast
  rfl

theorem headCell_selected (raw : Raw.Input d) (M : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw M env) (e : Expression)
    (nonnegative : 0 ≤ e.eval env memory) (inside : e.eval env memory ≤ env 2) :
    (headCell d e).eval env memory =
      if e.eval env memory < 2*env 6 then (sourceFact e).eval env memory
      else if e.eval env memory < 3*env 6 then 0
      else if e.eval env memory < 3*env 6+2*env 6*env 11 then
        (unaryHead d (mask (sub e (three numVars)))).eval env memory
      else (flag d (sub e (add (three numVars) (mul (two numVars) edges)))).eval env memory*env 12 := by
  have lengthPositive : 0 < env 2 := by rw [header.length]; positivity
  have variableNonnegative : 0 ≤ env 6 := by rw [header.numVars]; positivity
  have edgeNonnegative : 0 ≤ env 11 := by rw [header.edges]; positivity
  have thresholds : 3*env 6+2*env 6*env 11 ≤ env 2 := by
    rw [header.length,header.numVars,header.edges]
    norm_cast
    omega
  unfold headCell
  repeat rw [select_eval]
  all_goals try simp only [two,three,add_eval,mul_eval,constant_eval,input_eval]
  all_goals nlinarith

theorem atomCell_selected (raw : Raw.Input d) (M : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw M env) (e : Expression)
    (nonnegative : 0 ≤ e.eval env memory) (inside : e.eval env memory ≤ env 2) :
    (atomCell d e).eval env memory =
      if e.eval env memory < 2*env 6 then (oppositeTarget e).eval env memory
      else (unaryAtom d (mask (sub e (two numVars)))).eval env memory := by
  have lengthPositive : 0 < env 2 := by rw [header.length]; positivity
  have variableNonnegative : 0 ≤ env 6 := by rw [header.numVars]; positivity
  have threshold : 2*env 6 ≤ env 2 := by
    rw [header.length,header.numVars]
    norm_cast
    omega
  unfold atomCell
  rw [select_eval]
  all_goals try simp only [two,mul_eval,constant_eval,input_eval]
  all_goals omega

theorem ruleCell_selected (raw : Raw.Input d) (M : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (header : Metadata raw M env) (e : Expression)
    (nonnegative : 0 ≤ e.eval env memory) (inside : e.eval env memory ≤ env 2) :
    (ruleCell e).eval env memory =
      if e.eval env memory < 2*env 6 then 2*env 6+e.eval env memory/2
      else 3*env 6+(mask (sub e (two numVars))).eval env memory := by
  have lengthPositive : 0 < env 2 := by rw [header.length]; positivity
  have variableNonnegative : 0 ≤ env 6 := by rw [header.numVars]; positivity
  have threshold : 2*env 6 ≤ env 2 := by
    rw [header.length,header.numVars]
    norm_cast
    omega
  unfold ruleCell
  rw [select_eval]
  all_goals try simp only [two,three,add_eval,div_eval,mul_eval,constant_eval,input_eval]
  all_goals omega

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
