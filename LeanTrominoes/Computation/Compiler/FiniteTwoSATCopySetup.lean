/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATAssignments
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellExpressions

/-! # Concrete register setup around the original-input copying loop -/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression.CopySetup
open ComplexityAbstract.RAM LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells

abbrev Env := Fin 17 → ℤ

def prepare : List (Assignment 17) := [⟨2,.load (.constant 0)⟩,⟨3,.inputValue 5⟩]
def resume : List (Assignment 17) := [⟨1,.constant 0⟩,⟨2,.inputValue 16⟩,⟨3,.constant 0⟩]

theorem prepare_cost : Assignment.cost prepare = 6 := rfl
theorem resume_cost : Assignment.cost resume = 7 := rfl

theorem prepare_small (a : Assignment 17) (member : a ∈ prepare) : a.expression.nodes ≤ 2 := by
  simp only [prepare,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide

theorem resume_small (a : Assignment 17) (member : a ∈ resume) : a.expression.nodes ≤ 2 := by
  simp only [resume,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem prepare_safe {w cap count : ℕ} (env : Env) (memory : ℕ → ℤ)
    (arena : env 5 = cap) (unit : env 4 = 1) (inputLength : memory 0 = count)
    (word : Fits w cap) (inputWord : Fits w count) (oneWord : Fits w 1) :
    Assignment.Safe w 4 prepare env memory := by
  have zeroWord : Fits w 0 := Allocation.nat_fits_le (a:=0) (b:=1) oneWord (by omega)
  have address : (0 : ℤ) < (2^w : ℕ) := by positivity
  simp only [prepare,Assignment.Safe,Assignment.update,Expr.Safe,Expr.eval,
    Int.toNat_zero,inputLength,arena,unit,Function.update_apply]
  exact ⟨⟨zeroWord,by omega,address,inputWord⟩,word,oneWord⟩

theorem resume_safe {w count : ℕ} (env : Env) (memory : ℕ → ℤ)
    (length : env 16 = count) (unit : env 4 = 1)
    (word : Fits w count) (oneWord : Fits w 1) :
    Assignment.Safe w 4 resume env memory := by
  have zeroWord : Fits w 0 := Allocation.nat_fits_le (a:=0) (b:=1) oneWord (by omega)
  simp only [resume,Assignment.Safe,Assignment.update,Expr.Safe,Expr.eval,
    length,unit,Function.update_apply]
  exact ⟨zeroWord,word,zeroWord,oneWord⟩

theorem prepare_values (env : Env) (memory : ℕ → ℤ) :
    Assignment.evaluate prepare env memory = Function.update (Function.update env 2 (memory 0)) 3 (env 5) := by
  simp [prepare,Assignment.evaluate,Assignment.update,Expr.eval,Function.update_apply]

theorem resume_values (env : Env) (memory : ℕ → ℤ) :
    Assignment.evaluate resume env memory = Function.update (Function.update (Function.update env 1 0) 2 (env 16)) 3 0 := by
  simp [resume,Assignment.evaluate,Assignment.update,Expr.eval,Function.update_apply]

end LeanTrominoes.ImplicationGraph.TwoSATExpression.CopySetup
