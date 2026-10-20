/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATTable
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBudgets

/-! # Copying a word table toward lower addresses

Forward copying is safe even when the ranges overlap: each destination word
lies below every source word that has not yet been read.
-/
namespace LeanTrominoes.RAMTableCopy
open ComplexityAbstract.RAM ImplicationGraph.TwoSATExpression

def expression (k : ℕ) : Expr (k+6) :=
  .load (.arithmetic .add (.inputValue 5) (.inputValue 1))

theorem expression_nodes (k : ℕ) : (expression k).nodes=4 := rfl

theorem exec {k w source target count : ℕ} (data : Data (expression k).registers)
    (towardLower : target≤source)
    (controls : Table.Controls (k:=k+1) (expression k) data 0 count target)
    (sourceValue : data.1 (Table.reg (expression k) 5)=source)
    (sourceFits : Fits w (source+count : ℕ)) (targetFits : Fits w (target+count : ℕ))
    (valueFits : ∀ i, i < count → Fits w (data.2 (source+i))) :
    ∃ result, Structured.Exec w (Table.program (expression k)) data result (9*count+2) ∧
      Table.Controls (k:=k+1) (expression k) result count count target ∧
      result.2=prefixMemory data.2 target (fun i => data.2 (source+i)) count ∧
      ∀ j : Fin (k+6), 5 ≤ j.val → result.1 (Table.reg (expression k) j)=data.1 (Table.reg (expression k) j) := by
  let values : ℕ → ℤ := fun i => data.2 (source+i)
  let parameters := fun j : Fin (k+6) => data.1 (Table.reg (expression k) j)
  have addressFits (i : ℕ) (hi : i < count) : Fits w (target+i : ℕ) :=
    Allocation.nat_fits_le targetFits (by omega)
  have nextFits (i : ℕ) (hi : i < count) : Fits w (i+1 : ℕ) :=
    Allocation.nat_fits_le targetFits (by omega)
  have contract (i : ℕ) (hi : i < count) (current : Data (expression k).registers)
      (currentControls : Table.Controls (k:=k+1) (expression k) current i count target)
      (memory : current.2=prefixMemory data.2 target values i)
      (params : ∀ j : Fin (k+6), 5 ≤ j.val → current.1 (Table.reg (expression k) j)=parameters j) :
      (expression k).Safe w (fun j => current.1 (Table.reg (expression k) j)) current.2 ∧
        (expression k).eval (fun j => current.1 (Table.reg (expression k) j)) current.2=values i ∧ Fits w (values i) := by
    have index : current.1 (Table.reg (expression k) 1)=i := currentControls.1
    have sourceRegister : current.1 (Table.reg (expression k) 5)=source := by
      rw [params _ (by change 5%(k+6) ≤ 5%(k+6); omega)]
      exact sourceValue
    have original : current.2 (source+i)=values i := by
      rw [memory]
      unfold prefixMemory
      rw [ite_eq_right (by omega : ¬(target≤source+i ∧ source+i<target+i))]
    have indexFits : Fits w (i : ℕ) := Allocation.nat_fits_le sourceFits (by omega)
    have sourceWord : Fits w (source : ℕ) := Allocation.nat_fits_le sourceFits (by omega)
    have combined : Fits w ((source : ℤ)+i) := by
      simpa only [Nat.cast_add] using Allocation.nat_fits_le sourceFits (show source+i≤source+count by omega)
    have address : (source+i : ℕ)<(2^w : ℕ) := by
      exact_mod_cast Allocation.nat_address (Allocation.nat_fits_le sourceFits (show source+i≤source+count by omega))
    have asNat : ((source : ℤ)+i).toNat=source+i := by omega
    dsimp only [expression] at sourceRegister index
    refine ⟨?_,?_,valueFits i hi⟩
    · simp only [expression, Expr.Safe, Expr.eval, Arithmetic.eval, sourceRegister, index]
      exact ⟨⟨sourceWord,indexFits,combined⟩,by omega,by exact_mod_cast address,
        by simpa only [asNat,original] using valueFits i hi⟩
    · simp only [expression,Expr.eval,Arithmetic.eval,sourceRegister,index,asNat,original]
  obtain ⟨result,run,finalControls,finalMemory,preserved⟩ := Table.loop_exec (k:=k+1) (expression k)
    data.2 values parameters addressFits nextFits contract count 0 (by omega) data controls
      (by rw [prefixMemory_zero]) (fun _ _ => rfl)
  exact ⟨result,by simpa only [expression_nodes,Nat.reduceAdd] using run,finalControls,finalMemory,preserved⟩

end LeanTrominoes.RAMTableCopy
