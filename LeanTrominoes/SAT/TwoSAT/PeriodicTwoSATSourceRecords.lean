/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawFields
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellExpressions

/-! # Reading copied original clause records during table generation -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {n d : ℕ}

def SourceAt (input : Input d) (base : ℕ) (memory : ℕ → ℤ) : Prop :=
  ∀ j, j<(words input).length → memory (base+j)=(words input)[j]?.getD 0

def recordIndex (input : Input d) (i : ℤ) : Fin (records input).length :=
  ⟨(i%(input.2.length+1 : ℕ)).toNat,by
    have positive : (0:ℤ)<(input.2.length+1 : ℕ) := by omega
    have nonnegative := Int.emod_nonneg i (by omega : ((input.2.length+1 : ℕ) : ℤ)≠0)
    have smaller := Int.emod_lt_of_pos i positive
    simp only [records,List.length_append,List.length_cons,List.length_nil]
    omega⟩

def recordAt (input : Input d) (i : ℤ) : Clause (Fin input.1) d :=
  (records input)[(recordIndex input i).val]

theorem recordIndex_value (input : Input d) (i : ℤ) :
    ((recordIndex input i).val : ℤ)=i%(input.2.length+1 : ℕ) := by
  dsimp only [recordIndex]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))]

theorem record_word (input : Input d) (i : Fin (records input).length)
    (j : ℕ) (inside : j<recordSize d) :
    (words input)[2+i.val*recordSize d+j]?=(clauseWords (records input)[i.val])[j]? := by
  simp only [words]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  have index : 2+i.val*recordSize d+j-2=i.val*recordSize d+j := by omega
  rw [index]
  exact fixedBlock_get (records input) clauseWords (recordSize d) clauseWords_length i.val i.isLt j inside

theorem record_address_bound (input : Input d) (i : Fin (records input).length)
    (j : ℕ) (inside : j<recordSize d) : 2+i.val*recordSize d+j<(words input).length := by
  rw [words_length]
  have indexBound : i.val+1≤ input.2.length+1 := by
    have := i.isLt
    simp only [records,List.length_append,List.length_cons,List.length_nil] at this
    omega
  have products := Nat.mul_le_mul_right (recordSize d) indexBound
  rw [Nat.add_mul,Nat.one_mul] at products
  nlinarith

theorem record_eval (input : Input d) (base : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : SourceAt input base memory) (baseValue : env 5=base) (clauseCount : env 7=input.2.length)
    (clause : Cells.Expression) (j : ℕ) (inside : j<recordSize d) :
    (Cells.record d clause (Cells.constant j)).eval env memory=
      (clauseWords (recordAt input (clause.eval env memory)))[j]?.getD 0 := by
  let i := recordIndex input (clause.eval env memory)
  have modValue : clause.eval env memory%(input.2.length+1 : ℕ)=(i.val : ℤ) :=
    (recordIndex_value input _).symm
  simp only [Nat.cast_add,Nat.cast_one] at modValue
  have address : ((base : ℤ)+2+((recordSize d : ℕ) : ℤ)*(i.val : ℤ)+(j : ℕ)).toNat=
      base+(2+i.val*recordSize d+j) := by
    rw [show (base : ℤ)+2+((recordSize d : ℕ) : ℤ)*(i.val : ℤ)+(j : ℕ)=
      ((base+(2+i.val*recordSize d+j) : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  have table := source (2+i.val*recordSize d+j) (record_address_bound input i j inside)
  rw [record_word input i j inside] at table
  simp only [Cells.record,Cells.add,Cells.mul,Cells.mod,Cells.increment,Cells.clauses,Cells.original,
    Cells.input,Cells.constant,Expr.eval,Arithmetic.eval,baseValue,clauseCount,modValue]
  rw [show (base : ℤ)+2+((recordSize d : ℕ) : ℤ)*(i.val : ℤ)+(j : ℕ)=
    (base : ℤ)+2+(((recordSize d : ℕ) : ℤ)*(i.val : ℤ)+(j : ℕ)) by ring] at address
  rw [address]
  exact table

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
