/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellControl
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATArcFields

/-! # Evaluation identities for the original-record arithmetic expression -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d : ℕ}

@[simp] theorem constant_eval (value : ℤ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (constant value).eval env memory=value := rfl
@[simp] theorem input_eval (i : Fin 17) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (input i).eval env memory=env i := rfl
@[simp] theorem add_eval (a b : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (add a b).eval env memory=a.eval env memory+b.eval env memory := rfl
@[simp] theorem sub_eval (a b : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (sub a b).eval env memory=a.eval env memory-b.eval env memory := rfl
@[simp] theorem mul_eval (a b : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (mul a b).eval env memory=a.eval env memory*b.eval env memory := rfl
@[simp] theorem div_eval (a b : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (div a b).eval env memory=a.eval env memory/b.eval env memory := rfl
@[simp] theorem mod_eval (a b : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (mod a b).eval env memory=a.eval env memory%b.eval env memory := rfl

@[simp] theorem power_eval (j : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (power j).eval env memory=(env 8)^j := by induction j <;> simp_all [power,pow_succ]

theorem sourceLiteral_field (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=raw.2.length)
    (e : Expression) :
    (flag d (clauseIndex e)).eval env memory*(sourceLiteral d e).eval env memory=
      rawSourceLiteral (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory) := by
  have f0 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 0 (by dsimp [Raw.recordSize]; omega)
  have f1 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 1 (by dsimp [Raw.recordSize]; omega)
  have f2 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 2 (by dsimp [Raw.recordSize]; omega)
  have f3 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 3 (by dsimp [Raw.recordSize]; omega)
  have f4 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 4 (by dsimp [Raw.recordSize]; omega)
  norm_num at f0 f1 f2 f3 f4
  simp only [flag,sourceLiteral,two,complement,add_eval,mul_eval,sub_eval,constant_eval]
  rw [f0,f1,f2,f3,f4,Raw.flag_word,Raw.firstVariable_word,Raw.firstSign_word,Raw.secondVariable_word,Raw.secondSign_word]
  simp only [Option.getD_some,rawSourceLiteral]
  ring

theorem targetLiteral_field (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=raw.2.length)
    (e : Expression) :
    (flag d (clauseIndex e)).eval env memory*(targetLiteral d e).eval env memory=
      rawTargetLiteral (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory) := by
  have f0 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 0 (by dsimp [Raw.recordSize]; omega)
  have f1 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 1 (by dsimp [Raw.recordSize]; omega)
  have f2 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 2 (by dsimp [Raw.recordSize]; omega)
  have f3 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 3 (by dsimp [Raw.recordSize]; omega)
  have f4 := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) 4 (by dsimp [Raw.recordSize]; omega)
  norm_num at f0 f1 f2 f3 f4
  simp only [flag,targetLiteral,two,complement,sub_eval,add_eval,mul_eval,constant_eval]
  rw [f0,f1,f2,f3,f4,Raw.flag_word,Raw.firstVariable_word,Raw.firstSign_word,Raw.secondVariable_word,Raw.secondSign_word]
  simp only [Option.getD_some,rawTargetLiteral]

theorem displacement_field (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=raw.2.length)
    (e : Expression) (j : Fin d) :
    (displacement d e j).eval env memory=
      rawDisplacement (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory) j := by
  have fA := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) (5+j.val) (by dsimp [Raw.recordSize]; omega)
  have fB := Raw.record_eval raw sourceBase env memory source baseValue clauseCount (clauseIndex e) (5+d+j.val) (by dsimp [Raw.recordSize]; omega)
  push_cast at fA fB
  simp only [displacement,complement,add_eval,mul_eval,sub_eval,constant_eval]
  rw [fA,fB,Raw.firstOffset_word,Raw.secondOffset_word]
  simp only [Option.getD_some,rawDisplacement]

theorem shifted_eval (e : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ) :
    (shifted d e).eval env memory=∑ j : Fin d,
      (((row e).eval env memory/(env 8)^j.val%(env 8)+(displacement d e j).eval env memory)%(env 8))*(env 8)^j.val := by
  have fold (items : List (Fin d)) :
      (items.foldr (fun j rest => add
        (mul (mod (add (mod (div (row e) (power j.val)) period) (displacement d e j)) period)
          (power j.val)) rest) (constant 0)).eval env memory=
        (items.map (fun j => (((row e).eval env memory/(env 8)^j.val%(env 8)+
          (displacement d e j).eval env memory)%(env 8))*(env 8)^j.val)).sum := by
    induction items with
    | nil => simp
    | cons j items ih => simp [ih]
  simpa only [shifted,← List.ofFn_eq_map,List.sum_ofFn] using fold (List.finRange d)

theorem sourceVertex_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=raw.2.length)
    (e : Expression) :
    (sourceVertex d e).eval env memory=
      rawSourceLiteral (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory)*env 9+
        (row e).eval env memory := by
  simp only [sourceVertex,add_eval,mul_eval,coordinates,input_eval]
  rw [sourceLiteral_field raw sourceBase env memory source baseValue clauseCount e]

theorem targetVertex_eval (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5=sourceBase) (clauseCount : env 7=raw.2.length)
    (e : Expression) :
    (targetVertex d e).eval env memory=
      rawTargetLiteral (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory)*env 9+
        ∑ j : Fin d, (((row e).eval env memory/(env 8)^j.val%(env 8)+
          rawDisplacement (Raw.recordAt raw ((clauseIndex e).eval env memory)) ((direction e).eval env memory) j)%(env 8))*(env 8)^j.val := by
  simp only [targetVertex,add_eval,mul_eval,coordinates,input_eval]
  rw [targetLiteral_field raw sourceBase env memory source baseValue clauseCount e,shifted_eval]
  simp only [displacement_field raw sourceBase env memory source baseValue clauseCount e]

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
