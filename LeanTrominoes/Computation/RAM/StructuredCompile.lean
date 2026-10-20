/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Structured

/-! # Structured executions compile to primitive RAM executions

The simulation preserves every instruction count. This is the connection
between compositional program proofs and `RAM.DecidesWithin`.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Structured

/-- A successful structured execution gives an equally long primitive trace
in any containing program. Every compiled control address must fit a word. -/
theorem Exec.compiles {r w pc : ℕ} {program : List (Instruction r)} {code : Code r}
    {data result : Data r} {n : ℕ} (execution : Exec w code data result n)
    (contained : Contains program pc (code.assemble pc)) (capacity : pc+code.size<2^w) :
    RunsTo w program (data.at pc) (result.at (pc+code.size)) n := by
  induction execution generalizing pc with
  | @atom op data result evaluation =>
    apply RunsTo.single
    exact Primitive.compiles (by simpa [Code.assemble] using contained.singleton)
      (by simp only [Code.size] at capacity; omega) capacity evaluation
  | @seq a b data middle result n m first second ihFirst ihSecond =>
    simp only [Code.assemble] at contained
    have one := ihFirst contained.append_left (by simp only [Code.size] at capacity; omega)
    have two := ihSecond (pc := pc+a.size)
      (by simpa only [Code.assemble_length] using contained.append_right)
      (by simp only [Code.size] at capacity; omega)
    simpa only [Code.size,Nat.add_assoc] using one.trans two
  | @branch_yes c yes no data result n holds yesExec ih =>
    simp only [Code.assemble,List.append_assoc] at contained
    have jump := RunsTo.single (Condition.step_yes (w := w) contained.append_left.singleton
      (by simp only [Code.size] at capacity; omega)
      (by simp only [Code.size] at capacity; omega) holds)
    have body := ih (pc := pc+no.size+2)
      (by
        have location : pc+1+no.size+1=pc+no.size+2 := by omega
        simpa only [Code.assemble_length,List.length_singleton,location]
          using contained.append_right.append_right.append_right)
      (by simp only [Code.size] at capacity; omega)
    simpa only [Code.size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using jump.trans body
  | @branch_no c yes no data result n absent noExec ih =>
    simp only [Code.assemble,List.append_assoc] at contained
    have branch := RunsTo.single (Condition.step_no (w := w) contained.append_left.singleton
      (by simp only [Code.size] at capacity; omega)
      (by simp only [Code.size] at capacity; omega) absent)
    have body := ih (pc := pc+1)
      (by simpa only [List.length_singleton] using contained.append_right.append_left)
      (by simp only [Code.size] at capacity; omega)
    have jump : RunsTo w program (result.at (pc+1+no.size))
        (result.at (pc+(.branch c yes no : Code r).size)) 1 := run_jump (w := w) (data := result)
      (by simpa only [Code.size,Code.assemble_length,List.length_singleton,Nat.add_assoc]
        using contained.append_right.append_right.append_left.singleton)
      (by simp only [Code.size] at capacity; omega) capacity
    simpa only [Code.size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using (branch.trans body).trans jump
  | @loop_done c body data absent =>
    simp only [Code.assemble,List.append_assoc] at contained
    have first : program[pc]?=some (c.instruction (pc+2)) := by
      simpa using contained.append_left 0 (by simp)
    have second : program[pc+1]?=some (.jump (pc+body.size+3)) := by
      simpa using contained.append_left 1 (by simp)
    have branch := RunsTo.single (Condition.step_no (w := w) first
      (by simp only [Code.size] at capacity; omega)
      (by simp only [Code.size] at capacity; omega) absent)
    have jump := run_jump (w := w) (data := data) second (by simp only [Code.size] at capacity; omega) capacity
    simpa only [Code.size,Nat.add_assoc] using branch.trans jump
  | @loop_more c body data middle result n m holds bodyExec loopExec ihBody ihLoop =>
    simp only [Code.assemble,List.append_assoc] at contained
    have first : program[pc]?=some (c.instruction (pc+2)) := by
      simpa using contained.append_left 0 (by simp)
    have branch := RunsTo.single (Condition.step_yes (w := w) first
      (by simp only [Code.size] at capacity; omega)
      (by simp only [Code.size] at capacity; omega) holds)
    have bodyRun := ihBody (pc := pc+2)
      (by simpa only [List.length_cons,List.length_nil] using contained.append_right.append_left)
      (by simp only [Code.size] at capacity; omega)
    have back : RunsTo w program (middle.at (pc+2+body.size)) (middle.at pc) 1 :=
      run_jump (w := w) (data := middle)
      (by simpa only [List.length_cons,List.length_nil,Code.assemble_length]
        using contained.append_right.append_right.singleton)
      (by simp only [Code.size] at capacity; omega)
      (by simp only [Code.size] at capacity; omega)
    have rest := ihLoop (pc := pc) (by simpa only [Code.assemble,List.append_assoc] using contained) capacity
    simpa only [Code.size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using ((branch.trans bodyRun).trans back).trans rest

def Code.program {r : ℕ} (code : Code r) (output : Fin r) : List (Instruction r) :=
  code.assemble 0 ++ [.halt output]

/-- Compiling a complete program adds exactly one final halt instruction. -/
theorem Exec.halts {r w : ℕ} {code : Code r} {data result : Data r} {n : ℕ} {output : Fin r}
    (execution : Exec w code data result n) (capacity : code.size<2^w)
    (outputFits : Fits w (result.1 output)) :
    Executes w (code.program output) (data.at 0) (result.1 output) (n+1) := by
  have trace : RunsTo w (code.program output) (data.at 0) (result.at code.size) n := by
    simpa only [Nat.zero_add,Code.program] using execution.compiles (Contains.append _ [.halt output]) (by simpa using capacity)
  have fetch : (code.program output)[code.size]?=some (.halt output) := by
    simp [Code.program,← Code.assemble_length code 0 ]
  have halted : Executes w (code.program output) (result.at code.size) (result.1 output) 1 :=
    .halt (by simp [step,Data.at,fetch,not_le.mpr capacity,outputFits])
  exact trace.executes halted

/-- A compositional operational certificate yields the public RAM time property.
The program is fixed across all inputs and word sizes. -/
theorem decidesWithin {A : Type} {r : ℕ} (code : Code r) (output : Fin r)
    (encode : A → List ℤ) (p : A → Prop) (bound requiredBits : A → ℕ)
    (verified : ∀ a w, requiredBits a≤w → InputFits w (encode a) →
      code.size<2^w ∧ ∃ result n,
        Exec w code (initial (r := r) (encode a)).data result n ∧ n+1≤bound a ∧
        Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
        (result.1 output=1 ↔ p a)) : DecidesWithin encode p bound requiredBits := by
  refine ⟨r,code.program output,fun a w width inputFits => ?_⟩
  obtain ⟨capacity,result,n,execution,time,outputFits,boolean,correct⟩ := verified a w width inputFits
  exact ⟨n+1,result.1 output,execution.halts capacity outputFits,time,boolean,correct⟩

end LeanTrominoes.ComplexityAbstract.RAM.Structured
