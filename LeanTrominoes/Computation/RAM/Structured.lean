/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Execution

/-! # Structured assembly for the bounded-word RAM

Only the original register, arithmetic, load, and store instructions are
primitive. Branches and loops assemble into static jumps. Successful structured
executions check word bounds and carry the exact primitive instruction count.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Structured

inductive Primitive (r : ℕ)
  | constant (dst : Fin r) (value : ℤ)
  | copy (dst src : Fin r)
  | arithmetic (op : Arithmetic) (dst left right : Fin r)
  | load (dst address : Fin r)
  | store (address src : Fin r)

def Primitive.instruction {r : ℕ} : Primitive r → Instruction r
  | .constant dst value => .constant dst value
  | .copy dst src => .copy dst src
  | .arithmetic op dst left right => .arithmetic op dst left right
  | .load dst address => .load dst address
  | .store address src => .store address src

def Primitive.eval {r : ℕ} (w : ℕ) (op : Primitive r) (data : Data r) : Option (Data r) :=
  let set (dst : Fin r) (value : ℤ) :=
    if Fits w value then some (Function.update data.1 dst value,data.2) else none
  match op with
  | .constant dst value => set dst value
  | .copy dst src => set dst (data.1 src)
  | .arithmetic op dst left right => set dst (op.eval (data.1 left) (data.1 right))
  | .load dst address =>
    if data.1 address<0 ∨ data.1 address≥(2^w:ℕ) then none
    else set dst (data.2 (data.1 address).toNat)
  | .store address src =>
    if data.1 address<0 ∨ data.1 address≥(2^w:ℕ) ∨ ¬Fits w (data.1 src) then none
    else some (data.1,Function.update data.2 (data.1 address).toNat (data.1 src))

/-- Every primitive evaluation is one actual RAM instruction, including its
word checks. The separate PC condition accounts for its placement in code. -/
theorem Primitive.compiles {r w pc : ℕ} {program : List (Instruction r)} {op : Primitive r}
    {data result : Data r} (fetch : program[pc]?=some op.instruction)
    (source : pc<2^w) (destination : pc+1<2^w) (evaluation : op.eval w data=some result) :
    step w program (data.at pc)=.next (result.at (pc+1)) := by
  rcases data with ⟨regs,mem⟩
  rcases result with ⟨regs',mem'⟩
  simp only [step,Data.at,not_le.mpr source,ite_false,fetch]
  cases op <;> simp only [Primitive.eval,Primitive.instruction] at evaluation ⊢
  all_goals
    simp only [write,next,writeRegister,destination,ite_true]
  all_goals split_ifs at evaluation ⊢
  all_goals simp_all
  all_goals rcases evaluation with ⟨rfl,rfl⟩; rfl

inductive Condition (r : ℕ)
  | eq (left right : Fin r)
  | lt (left right : Fin r)

def Condition.Holds {r : ℕ} : Condition r → Data r → Prop
  | .eq a b, data => data.1 a=data.1 b
  | .lt a b, data => data.1 a<data.1 b

instance {r : ℕ} (c : Condition r) (data : Data r) : Decidable (c.Holds data) :=
  match c with
  | .eq a b => inferInstanceAs (Decidable (data.1 a=data.1 b))
  | .lt a b => inferInstanceAs (Decidable (data.1 a<data.1 b))

def Condition.instruction {r : ℕ} : Condition r → ℕ → Instruction r
  | .eq a b, target => .branchEq a b target
  | .lt a b, target => .branchLt a b target

theorem Condition.step_yes {r w pc target : ℕ} {program : List (Instruction r)}
    {c : Condition r} {data : Data r} (fetch : program[pc]?=some (c.instruction target))
    (source : pc<2^w) (destination : target<2^w) (holds : c.Holds data) :
    step w program (data.at pc)=.next (data.at target) := by
  cases c <;> simp only [Condition.Holds] at holds <;>
    simp [Condition.instruction,step,Data.at,next,fetch,not_le.mpr source,holds,destination]

theorem Condition.step_no {r w pc target : ℕ} {program : List (Instruction r)}
    {c : Condition r} {data : Data r} (fetch : program[pc]?=some (c.instruction target))
    (source : pc<2^w) (destination : pc+1<2^w) (holds : ¬c.Holds data) :
    step w program (data.at pc)=.next (data.at (pc+1)) := by
  cases c <;> simp only [Condition.Holds] at holds <;>
    simp [Condition.instruction,step,Data.at,next,fetch,not_le.mpr source,holds,destination]

inductive Code (r : ℕ)
  | atom (op : Primitive r)
  | seq (first second : Code r)
  | branch (condition : Condition r) (yes no : Code r)
  | loop (condition : Condition r) (body : Code r)

namespace Code

def size {r : ℕ} : Code r → ℕ
  | .atom _ => 1
  | .seq a b => a.size+b.size
  | .branch _ yes no => no.size+yes.size+2
  | .loop _ body => body.size+3

def assemble {r : ℕ} : Code r → ℕ → List (Instruction r)
  | .atom op, _ => [op.instruction]
  | .seq a b, pc => a.assemble pc ++ b.assemble (pc+a.size)
  | .branch c yes no, pc =>
    [c.instruction (pc+no.size+2)] ++ no.assemble (pc+1) ++
      [.jump (pc+no.size+yes.size+2)] ++ yes.assemble (pc+no.size+2)
  | .loop c body, pc =>
    [c.instruction (pc+2),.jump (pc+body.size+3)] ++
      body.assemble (pc+2) ++ [.jump pc]

theorem assemble_length {r : ℕ} (code : Code r) (pc : ℕ) : (code.assemble pc).length=code.size := by
  induction code generalizing pc <;> simp_all [assemble,size]
  all_goals omega

end Code

/-- The rules count precisely the instructions emitted by `Code.assemble`.
There is no rule for executing an arbitrary Lean function in one step. -/
inductive Exec {r : ℕ} (w : ℕ) : Code r → Data r → Data r → ℕ → Prop
  | atom {op data result} : op.eval w data=some result → Exec w (.atom op) data result 1
  | seq {a b data middle result n m} : Exec w a data middle n → Exec w b middle result m →
      Exec w (.seq a b) data result (n+m)
  | branch_yes {c yes no data result n} : c.Holds data → Exec w yes data result n →
      Exec w (.branch c yes no) data result (n+1)
  | branch_no {c yes no data result n} : ¬c.Holds data → Exec w no data result n →
      Exec w (.branch c yes no) data result (n+2)
  | loop_done {c body data} : ¬c.Holds data → Exec w (.loop c body) data data 2
  | loop_more {c body data middle result n m} : c.Holds data → Exec w body data middle n →
      Exec w (.loop c body) middle result m → Exec w (.loop c body) data result (n+m+2)

end LeanTrominoes.ComplexityAbstract.RAM.Structured
