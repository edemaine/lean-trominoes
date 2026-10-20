/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATTable
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBudgets

/-! # Copying original input words to a disjoint caller arena

This is a nine-instruction-per-word implementation using the verified flat
expression loop. Signed input values are checked directly by `InputFits`.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

def copyExpression (k : ℕ) : Expr (k+5) :=
  .load (.arithmetic .add (.inputValue 1) (.constant 1))

theorem copyExpression_nodes (k : ℕ) : (copyExpression k).nodes=4 := rfl

def InputAt (input : List ℤ) (memory : ℕ → ℤ) : Prop :=
  ∀ i, i< input.length → memory (i+1)=input[i]?.getD 0

theorem inputAt_initial (input : List ℤ) : InputAt input (initial (r := 1) input).memory := by
  intro i hi
  simp [initial]

theorem copy_exec {k w arena : ℕ} (input : List ℤ)
    (data : Data (copyExpression k).registers)
    (separate : input.length<arena)
    (inputFits : InputFits w input) (arenaFits : Fits w (arena+input.length : ℕ))
    (controls : Table.Controls (copyExpression k) data 0 input.length arena)
    (inputMemory : InputAt input data.2) :
    ∃ result, Structured.Exec w (Table.program (copyExpression k)) data result (9*input.length+2) ∧
      Table.Controls (copyExpression k) result input.length input.length arena ∧
      result.2=prefixMemory data.2 arena (fun i => input[i]?.getD 0) input.length ∧
      ∀ j : Fin (k+5), 5≤ j.val → result.1 (Table.reg (copyExpression k) j)=data.1 (Table.reg (copyExpression k) j) := by
  let values : ℕ → ℤ := fun i => input[i]?.getD 0
  let parameters := fun j : Fin (k+5) => data.1 (Table.reg (copyExpression k) j)
  have addressFits (i : ℕ) (hi : i< input.length) : Fits w (arena+i : ℕ) :=
    Allocation.nat_fits_le arenaFits (by omega)
  have nextFits (i : ℕ) (hi : i< input.length) : Fits w (i+1 : ℕ) :=
    Allocation.nat_fits_le inputFits.1 (by omega)
  have contract (i : ℕ) (hi : i< input.length) (current : Data (copyExpression k).registers)
      (currentControls : Table.Controls (copyExpression k) current i input.length arena)
      (memory : current.2=prefixMemory data.2 arena values i)
      (_params : ∀ j : Fin (k+5), 5≤ j.val → current.1 (Table.reg (copyExpression k) j)=parameters j) :
      (copyExpression k).Safe w (fun j => current.1 (Table.reg (copyExpression k) j)) current.2 ∧
        (copyExpression k).eval (fun j => current.1 (Table.reg (copyExpression k) j)) current.2=values i ∧ Fits w (values i) := by
    have index : current.1 (Table.reg (copyExpression k) 1)=i := currentControls.1
    have original : current.2 (i+1)=values i := by
      rw [memory]
      simp only [prefixMemory]
      rw [ite_eq_right (by omega : ¬(arena≤ i+1 ∧ i+1<arena+i))]
      exact inputMemory i hi
    have valueFits : Fits w (values i) := by
      dsimp [values]
      rw [List.getElem?_eq_getElem hi]
      exact inputFits.2 _ (List.getElem_mem hi)
    have loadAddress : (i+1 : ℕ)<(2^w : ℕ) := by exact_mod_cast Allocation.nat_address (nextFits i hi)
    have indexFits : Fits w i := Allocation.nat_fits_le inputFits.1 (by omega)
    have oneFits : Fits w 1 := Allocation.nat_fits_le (a := 1) inputFits.1 (by omega)
    have addFits := nextFits i hi
    simp only [Nat.cast_add,Nat.cast_one] at addFits
    simp only [copyExpression] at index
    have addressCast : ((i : ℤ)+1).toNat=i+1 := by omega
    refine ⟨?_,?_,valueFits⟩
    · simp only [copyExpression,Expr.Safe,Expr.eval,Arithmetic.eval,index]
      refine ⟨⟨indexFits,oneFits,addFits⟩,?_,?_,?_⟩
      · omega
      · exact_mod_cast loadAddress
      · simpa only [addressCast,original] using valueFits
    · simp only [copyExpression,Expr.eval,Arithmetic.eval,index,addressCast,original]

  obtain ⟨result,execution,finalControls,finalMemory,preserved⟩ := Table.loop_exec (copyExpression k)
    data.2 values parameters addressFits nextFits contract input.length 0 (by omega) data controls
      (by rw [prefixMemory_zero]) (fun _ _ => rfl)
  exact ⟨result,by simpa only [copyExpression_nodes,Nat.reduceAdd] using execution,finalControls,finalMemory,preserved⟩

end LeanTrominoes.ImplicationGraph.TwoSATExpression
