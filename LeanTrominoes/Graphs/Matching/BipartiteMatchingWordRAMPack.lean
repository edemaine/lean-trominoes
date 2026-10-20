/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTableCopyDown
import LeanTrominoes.Computation.Compiler.FiniteTwoSATAssignments
import LeanTrominoes.Computation.Compiler.FiniteTwoSATRegisters

/-! # Packing generated endpoint arrays into the ordinary matching input

Register-only setup uses a fixed scratch bank. The two forward copies admit
overlap with their source arrays; the untouched right array remains readable
after the left copy.
-/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM ImplicationGraph.TwoSATExpression

def input (i : Fin 86) : Fin 128 := i.castAdd 42

def environment (data : Data 128) : Fin 86 → ℤ := fun i => data.1 (input i)

def setup (right : Bool) : List (Assignment 86) :=
  [⟨1,.constant 0⟩,⟨2,.inputValue 83⟩,
   ⟨3,if right then .arithmetic .add (.constant 4) (.inputValue 83) else .constant 4⟩,
   ⟨4,.constant 1⟩,⟨5,.inputValue (if right then 71 else 70)⟩]

def setupCode (right : Bool) : Structured.Code 128 :=
  Assignment.sequence 42 (by decide) 4 (setup right)

theorem setup_exec {w source count : ℕ} (right : Bool) (data : Data 128)
    (sourceValue : data.1 (if right then 71 else 70)=source)
    (countValue : data.1 83=count)
    (sourceFits : Fits w source) (targetFits : Fits w (4+count : ℕ)) :
    ∃ result, Structured.Exec w (setupCode right) data result (if right then 13 else 11) ∧
      result.2=data.2 ∧
      result.1 1=0 ∧ result.1 2=count ∧
      result.1 3=(if right then 4+count else 4 : ℕ) ∧ result.1 4=1 ∧ result.1 5=source ∧
      (∀ j : Fin 128, 6 ≤ j.val → j.val < 86 → result.1 j=data.1 j) := by
  have four := Allocation.nat_fits_le (a:=4) targetFits (by omega)
  have zero := Allocation.nat_fits_le (a:=0) targetFits (by omega)
  have one := Allocation.nat_fits_le (a:=1) targetFits (by omega)
  have countFits := Allocation.nat_fits_le (a:=count) targetFits (by omega)
  have safe : Assignment.Safe w 4 (setup right) (environment data) data.2 := by
    cases right <;>
      simp_all [setup,Assignment.Safe,Assignment.update,Expr.Safe,Expr.eval,Arithmetic.eval,
        environment,input,countValue,sourceValue,Function.update_apply,sourceFits,
        countFits,zero,one,four,show Fits w (4+(count : ℤ)) by simpa only [Nat.cast_add,Nat.cast_ofNat] using targetFits]
  have small : ∀ a∈setup right, a.expression.nodes ≤ 42 := by
    cases right <;> simp [setup,Expr.nodes] <;> omega
  obtain ⟨result,run,memory,values⟩ := Assignment.sequence_exec (setup right) (by decide) small 4
    (environment data) data (fun _ => rfl) safe
  refine ⟨result,?_,memory,?_,?_,?_,?_,?_,?_⟩
  · cases right <;> simpa only [setupCode,setup,Assignment.cost,Expr.nodes,Nat.reduceAdd,Bool.false_eq_true,ite_false,ite_true] using run
  · cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at sourceValue
    all_goals simpa [setup,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,
      environment,input,Assignment.inputRegister,countValue,sourceValue,Function.update_apply,Nat.cast_add] using values 1
  · cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at sourceValue
    all_goals simpa [setup,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,
      environment,input,Assignment.inputRegister,countValue,sourceValue,Function.update_apply,Nat.cast_add] using values 2
  · cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at sourceValue
    all_goals simpa [setup,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,
      environment,input,Assignment.inputRegister,countValue,sourceValue,Function.update_apply,Nat.cast_add] using values 3
  · cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at sourceValue
    all_goals simpa [setup,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,
      environment,input,Assignment.inputRegister,countValue,sourceValue,Function.update_apply,Nat.cast_add] using values 4
  · cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at sourceValue
    all_goals simpa [setup,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,
      environment,input,Assignment.inputRegister,countValue,sourceValue,Function.update_apply,Nat.cast_add] using values 5
  · intro j lo hi
    let a : Fin 86 := ⟨j.val,hi⟩
    have same : input a=j := Fin.ext rfl
    rw [←same]
    change result.1 (Assignment.inputRegister 42 a)=_
    rw [values]
    dsimp only [setup,Assignment.evaluate,Assignment.update]
    have ne (i : Fin 86) (low : i.val ≤ 5) : a≠i := by intro eq; have := congrArg Fin.val eq; dsimp [a] at this; omega
    simp only [Function.update_of_ne (ne 1 (by decide)),Function.update_of_ne (ne 2 (by decide)),
      Function.update_of_ne (ne 3 (by decide)),Function.update_of_ne (ne 4 (by decide)),
      Function.update_of_ne (ne 5 (by decide))]
    rfl

def copyCode (right : Bool) : Structured.Code 128 :=
  .seq (setupCode right)
    ((Table.program (RAMTableCopy.expression 54)).widen (by decide : 64 ≤ 128))

theorem copy_exec {w source count : ℕ} (right : Bool) (data : Data 128)
    (sourceValue : data.1 (if right then 71 else 70)=source)
    (countValue : data.1 83=count)
    (towardLower : (if right then 4+count else 4 : ℕ) ≤ source)
    (sourceFits : Fits w (source+count : ℕ))
    (targetFits : Fits w ((if right then 4+count else 4)+count : ℕ))
    (valueFits : ∀ i, i < count → Fits w (data.2 (source+i))) :
    ∃ result, Structured.Exec w (copyCode right) data result
        ((if right then 13 else 11)+9*count+2) ∧
      result.2=prefixMemory data.2 (if right then 4+count else 4)
        (fun i => data.2 (source+i)) count ∧
      (∀ j : Fin 128, 64 ≤ j.val → j.val < 86 → result.1 j=data.1 j) := by
  have fourCount : 4+count ≤ (if right then 4+count else 4)+count := by cases right <;> simp <;> omega
  obtain ⟨ready,setupRun,setupMemory,index,length,base,one,sourceReg,params⟩ :=
    setup_exec right data sourceValue countValue
      (Allocation.nat_fits_le sourceFits (by omega))
      (Allocation.nat_fits_le targetFits fourCount)
  let low := ready.restrict (by decide : 64 ≤ 128)
  have controls : Table.Controls (k:=55) (RAMTableCopy.expression 54) low 0 count
      (if right then 4+count else 4) := by
    exact ⟨index,length,base,one⟩
  obtain ⟨copied,copyRun,_,copyMemory,_⟩ := RAMTableCopy.exec (k:=54) low towardLower controls
    sourceReg sourceFits targetFits (by simpa only [low,Data.restrict,setupMemory] using valueFits)
  obtain ⟨result,largeRun,memory,_,high⟩ := copyRun.widen_restrict (by decide : 64 ≤ 128)
  refine ⟨result,by simpa only [copyCode,Nat.add_assoc] using setupRun.seq largeRun,?_,?_⟩
  · simpa only [memory,copyMemory,low,Data.restrict,setupMemory]
  · intro j lo hi
    exact (high j lo).trans (params j (by omega) hi)

def copies : Structured.Code 128 := .seq (copyCode false) (copyCode true)

theorem copies_exec {w source count : ℕ} (data : Data 128)
    (left : data.1 70=source) (right : data.1 71=source+count) (edges : data.1 83=count)
    (lower : 4 ≤ source) (fits : Fits w (source+2*count : ℕ))
    (leftFits : ∀ i, i < count → Fits w (data.2 (source+i)))
    (rightFits : ∀ i, i < count → Fits w (data.2 (source+count+i))) :
    ∃ result, Structured.Exec w copies data result (18*count+28) ∧
      result.2=prefixMemory
        (prefixMemory data.2 4 (fun i => data.2 (source+i)) count)
        (4+count) (fun i => data.2 (source+count+i)) count ∧
      (∀ j : Fin 128, 64 ≤ j.val → j.val < 86 → result.1 j=data.1 j) := by
  obtain ⟨middle,first,firstMemory,firstParams⟩ := copy_exec (source:=source) (count:=count) false data left edges (by simpa using lower)
    (Allocation.nat_fits_le fits (by omega)) (by simpa using Allocation.nat_fits_le (a:=4+count) fits (by omega)) leftFits
  simp only [Bool.false_eq_true,ite_false] at firstMemory
  have rightUnchanged (i : ℕ) : middle.2 (source+count+i)=data.2 (source+count+i) := by
    rw [firstMemory]
    exact ite_eq_right (by omega)
  obtain ⟨result,second,secondMemory,secondParams⟩ := copy_exec (source:=source+count) (count:=count) true middle
    (by simpa [firstParams 71 (by decide) (by decide)] using right)
    (by simpa [firstParams 83 (by decide) (by decide)] using edges)
    (by simp only [ite_true]; omega) (by simpa only [Nat.add_assoc,two_mul] using fits)
    (by simpa using Allocation.nat_fits_le (a:=4+count+count) fits (by omega))
    (fun i hi => by simpa only [rightUnchanged] using rightFits i hi)
  simp only [ite_true] at secondMemory
  refine ⟨result,?_,?_,?_⟩
  · have run := first.seq second
    convert run using 1 <;> simp only [copies,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · rw [secondMemory,firstMemory]
    congr 1
    funext i
    simpa only [firstMemory] using rightUnchanged i
  · intro j lo hi
    exact (secondParams j lo hi).trans (firstParams j lo hi)

end LeanTrominoes.BipartiteMatching.PackWordRAM
