/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATSourceRecords
import LeanTrominoes.Computation.Compiler.FiniteTwoSATControl

/-! # Word certificates for original record fields and local differences -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {n d : ℕ}

theorem recordAt_member (input : Input d) (i : ℤ) : recordAt input i ∈ records input := by
  exact List.getElem_mem (recordIndex input i).isLt

theorem records_local (input : LocalInput d) : LocalDifferences (records input.val) := by
  intro a b member j
  have original : some (a,b) ∈ input.val.2 := by simpa [records] using member
  exact input.property a b original j

theorem record_difference (input : LocalInput d) (i : ℤ) (j : Fin d) :
    (secondOffset (recordAt input.val i) j-firstOffset (recordAt input.val i) j).natAbs≤1 := by
  have member := recordAt_member input.val i
  cases eq : recordAt input.val i with
  | none => simp [secondOffset,firstOffset]
  | some pair =>
    rcases pair with ⟨a,b⟩
    exact records_local input a b (by simpa only [eq] using member) j

theorem small_field (c : Clause (Fin n) d) (j : ℕ) (within : j<5) :
    ((clauseWords c)[j]?.getD 0).natAbs≤n+1 := by
  interval_cases j
  · rw [flag_word]
    cases c <;> simp [validFlag]
  · rw [firstVariable_word]
    cases c with
    | none => simp [firstVariable]
    | some pair => rcases pair with ⟨a,b⟩; simp only [Option.getD_some,firstVariable,Int.natAbs_natCast]; omega
  · rw [firstSign_word]
    cases c with
    | none => simp [firstSign]
    | some pair => rcases pair with ⟨a,b⟩; simp only [Option.getD_some,firstSign]; split_ifs <;> simp
  · rw [secondVariable_word]
    cases c with
    | none => simp [secondVariable]
    | some pair => rcases pair with ⟨a,b⟩; simp only [Option.getD_some,secondVariable,Int.natAbs_natCast]; omega
  · rw [secondSign_word]
    cases c with
    | none => simp [secondSign]
    | some pair => rcases pair with ⟨a,b⟩; simp only [Option.getD_some,secondSign]; split_ifs <;> simp

theorem field_mem_words (input : Input d) (i : ℤ) (j : ℕ) (inside : j<recordSize d) :
    (clauseWords (recordAt input i))[j]?.getD 0 ∈ words input := by
  have within : j<(clauseWords (recordAt input i)).length := by rw [clauseWords_length]; exact inside
  rw [List.getElem?_eq_getElem within]
  simp only [Option.getD_some]
  apply List.mem_append.mpr
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨recordAt input i,recordAt_member input i,List.getElem_mem within⟩

theorem record_valueFits (input : Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : SourceAt input sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=input.2.length)
    (clause : Cells.Expression) (j : ℕ) (inside : j<recordSize d) (w : ℕ)
    (inputFits : InputFits w (words input)) : Fits w ((Cells.record d clause (Cells.constant j)).eval env memory) := by
  rw [record_eval input sourceBase env memory source baseValue clauseCount clause j inside]
  exact inputFits.2 _ (field_mem_words input _ j inside)

def recordAddress (d : ℕ) (clause : Cells.Expression) (j : ℕ) : Cells.Expression :=
  Cells.add (Cells.add Cells.original (Cells.constant 2))
    (Cells.add (Cells.mul (Cells.constant (recordSize d)) (Cells.mod clause (Cells.increment Cells.clauses)))
      (Cells.constant j))

theorem recordAddress_nonnegative (input : Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (baseValue : env 5=sourceBase) (clauseCount : env 7=input.2.length) (clause : Cells.Expression) (j : ℕ) :
    0≤(recordAddress d clause j).eval env memory := by
  have modPositive : ((input.2.length : ℤ)+1)≠0 := by omega
  have nonnegative := Int.emod_nonneg (clause.eval env memory) modPositive
  simp only [recordAddress,Cells.add,Cells.mul,Cells.mod,Cells.increment,Cells.clauses,Cells.original,
    Cells.input,Cells.constant,Expr.eval,Arithmetic.eval,baseValue,clauseCount]
  positivity

theorem recordAddress_controlled {base : ℕ} (env : Fin 17 → ℤ) (memory : ℕ → ℤ) (raw : List ℤ)
    (parameters : ∀ i, i≠0 → (env i).natAbs≤base) (sizeBound : recordSize d≤base) (two : 2≤base)
    (clause : Cells.Expression) (clauseControlled : Controlled base env memory raw clause)
    (j : ℕ) (inside : j<recordSize d) : Controlled base env memory raw (recordAddress d clause j) := by
  simp only [recordAddress,Cells.add,Cells.mul,Cells.mod,Cells.increment,Cells.clauses,Cells.original,Cells.input,Cells.constant]
  repeat' first
    | exact clauseControlled
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact parameters _ (by decide)
    | apply Controlled.constant; norm_num <;> omega

theorem record_controlled {base : ℕ} (input : Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : SourceAt input sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=input.2.length)
    (parameters : ∀ i, i≠0 → (env i).natAbs≤base) (sizeBound : recordSize d≤base) (two : 2≤base)
    (variableBound : input.1+1≤base) (clause : Cells.Expression)
    (clauseControlled : Controlled base env memory (words input) clause) (j : ℕ) (inside : j<5) :
    Controlled base env memory (words input) (Cells.record d clause (Cells.constant j)) := by
  have fieldBound : j<recordSize d := by dsimp [recordSize]; omega
  change Controlled base env memory (words input) (.load (recordAddress d clause j))
  apply Controlled.load (recordAddress_controlled env memory (words input) parameters sizeBound two
    clause clauseControlled j fieldBound) (recordAddress_nonnegative input sourceBase env memory baseValue clauseCount clause j)
  change ((Cells.record d clause (Cells.constant j)).eval env memory).natAbs≤base
  rw [record_eval input sourceBase env memory source baseValue clauseCount clause j fieldBound]
  exact (small_field _ j inside).trans variableBound

theorem difference_controlled {base : ℕ} (input : LocalInput d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : SourceAt input.val sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=input.val.2.length)
    (parameters : ∀ i, i≠0 → (env i).natAbs≤base) (sizeBound : recordSize d≤base) (two : 2≤base)
    (clause : Cells.Expression) (clauseControlled : Controlled base env memory (words input.val) clause) (j : Fin d) :
    Controlled base env memory (words input.val)
      (Cells.sub (Cells.record d clause (Cells.constant (5+d+j.val))) (Cells.record d clause (Cells.constant (5+j.val)))) := by
  have firstBound : 5+j.val<recordSize d := by dsimp [recordSize]; omega
  have secondBound : 5+d+j.val<recordSize d := by dsimp [recordSize]; omega
  change Controlled base env memory (words input.val)
    (.arithmetic .sub (.load (recordAddress d clause (5+d+j.val))) (.load (recordAddress d clause (5+j.val))))
  apply Controlled.difference
    (recordAddress_controlled env memory (words input.val) parameters sizeBound two clause clauseControlled _ secondBound)
    (recordAddress_controlled env memory (words input.val) parameters sizeBound two clause clauseControlled _ firstBound)
    (recordAddress_nonnegative input.val sourceBase env memory baseValue clauseCount clause _)
    (recordAddress_nonnegative input.val sourceBase env memory baseValue clauseCount clause _)
    (record_valueFits input.val sourceBase env memory source baseValue clauseCount clause _ secondBound)
    (record_valueFits input.val sourceBase env memory source baseValue clauseCount clause _ firstBound)
  change ((Cells.record d clause (Cells.constant (5+d+j.val))).eval env memory-
    (Cells.record d clause (Cells.constant (5+j.val))).eval env memory).natAbs≤base
  have firstValue := record_eval input.val sourceBase env memory source baseValue clauseCount clause _ firstBound
  have secondValue := record_eval input.val sourceBase env memory source baseValue clauseCount clause _ secondBound
  push_cast at firstValue secondValue
  rw [secondValue,firstValue,secondOffset_word,firstOffset_word]
  simp only [Option.getD_some]
  exact (record_difference input _ j).trans (by omega)

theorem reverse_difference_controlled {base : ℕ} (input : LocalInput d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : SourceAt input.val sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=input.val.2.length)
    (parameters : ∀ i, i≠0 → (env i).natAbs≤base) (sizeBound : recordSize d≤base) (two : 2≤base)
    (clause : Cells.Expression) (clauseControlled : Controlled base env memory (words input.val) clause) (j : Fin d) :
    Controlled base env memory (words input.val)
      (Cells.sub (Cells.record d clause (Cells.constant (5+j.val))) (Cells.record d clause (Cells.constant (5+d+j.val)))) := by
  have firstBound : 5+j.val<recordSize d := by dsimp [recordSize]; omega
  have secondBound : 5+d+j.val<recordSize d := by dsimp [recordSize]; omega
  change Controlled base env memory (words input.val)
    (.arithmetic .sub (.load (recordAddress d clause (5+j.val))) (.load (recordAddress d clause (5+d+j.val))))
  apply Controlled.difference
    (recordAddress_controlled env memory (words input.val) parameters sizeBound two clause clauseControlled _ firstBound)
    (recordAddress_controlled env memory (words input.val) parameters sizeBound two clause clauseControlled _ secondBound)
    (recordAddress_nonnegative input.val sourceBase env memory baseValue clauseCount clause _)
    (recordAddress_nonnegative input.val sourceBase env memory baseValue clauseCount clause _)
    (record_valueFits input.val sourceBase env memory source baseValue clauseCount clause _ firstBound)
    (record_valueFits input.val sourceBase env memory source baseValue clauseCount clause _ secondBound)
  change ((Cells.record d clause (Cells.constant (5+j.val))).eval env memory-
    (Cells.record d clause (Cells.constant (5+d+j.val))).eval env memory).natAbs≤base
  have firstValue := record_eval input.val sourceBase env memory source baseValue clauseCount clause _ firstBound
  have secondValue := record_eval input.val sourceBase env memory source baseValue clauseCount clause _ secondBound
  push_cast at firstValue secondValue
  rw [secondValue,firstValue,secondOffset_word,firstOffset_word]
  simp only [Option.getD_some]
  have small := record_difference input (clause.eval env memory) j
  rw [← Int.natAbs_neg,neg_sub] at small
  exact small.trans (by omega)

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
