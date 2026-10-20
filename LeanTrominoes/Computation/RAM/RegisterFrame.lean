/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Structured

/-! # Registers outside a program's write footprint

A subprogram preserves each register that is never a destination. This applies
to private registers anywhere in the register file, including between scratch
registers used by other subprograms.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Structured

/-- The primitive never writes the specified register. -/
def Primitive.PreservesRegister {r : ℕ} (i : Fin r) : Primitive r → Prop
  | .constant dst _ => i ≠ dst
  | .copy dst _ => i ≠ dst
  | .arithmetic _ dst _ _ => i ≠ dst
  | .load dst _ => i ≠ dst
  | .store _ _ => True

/-- No instruction in the structured program writes this register. -/
def Code.PreservesRegister {r : ℕ} (i : Fin r) : Code r → Prop
  | .atom op => op.PreservesRegister i
  | .seq first second => first.PreservesRegister i ∧ second.PreservesRegister i
  | .branch _ yes no => yes.PreservesRegister i ∧ no.PreservesRegister i
  | .loop _ body => body.PreservesRegister i

theorem Primitive.eval_register {r w : ℕ} {op : Primitive r}
    {data result : Data r} {i : Fin r}
    (untouched : op.PreservesRegister i) (evaluation : op.eval w data = some result) :
    result.1 i = data.1 i := by
  cases op <;> simp only [Primitive.PreservesRegister] at untouched
  all_goals simp only [Primitive.eval] at evaluation
  all_goals split_ifs at evaluation
  all_goals cases evaluation
  all_goals simp_all [Function.update_of_ne]

/-- Exact register preservation, independent of the run's word width and cost. -/
theorem Exec.register_eq {r w : ℕ} {code : Code r} {data result : Data r} {cost : ℕ}
    (execution : Exec w code data result cost) {i : Fin r}
    (untouched : code.PreservesRegister i) : result.1 i = data.1 i := by
  induction execution with
  | atom evaluation => exact Primitive.eval_register untouched evaluation
  | seq first second ihFirst ihSecond => exact (ihSecond untouched.2).trans (ihFirst untouched.1)
  | branch_yes holds body ih => exact ih untouched.1
  | branch_no absent body ih => exact ih untouched.2
  | loop_done absent => rfl
  | loop_more holds body rest ihBody ihRest => exact (ihRest untouched).trans (ihBody untouched)

end LeanTrominoes.ComplexityAbstract.RAM.Structured
