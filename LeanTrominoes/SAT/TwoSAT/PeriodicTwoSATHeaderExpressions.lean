/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATAssignments
import LeanTrominoes.Computation.Compiler.FiniteTwoSATDoubling
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellExpressions
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCoverCriterion

/-! # The arithmetic header of the periodic 2SAT word-RAM constructor

The fixed program loads the two original counts, computes the determinant
bound, doubles the period, and computes all Horn table sizes and arena bounds.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ImplicationGraph.TwoSATExpression Cells

abbrev Env := Fin 17 → ℤ
abbrev Statement := Assignment 17

def power (e : Expression) : ℕ → Expression
  | 0 => constant 1
  | d+1 => mul (power e d) e

@[simp] theorem power_eval (e : Expression) (d : ℕ) (env : Env) (memory : ℕ → ℤ) :
    (power e d).eval env memory=(e.eval env memory)^d := by
  induction d with
  | zero => simp [power,Cells.constant,Expr.eval]
  | succ d ih => simp only [power,Cells.mul,Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,ih,pow_succ]

def determinant (d : ℕ) : Expression :=
  mul (constant d.factorial) (power (add (mul (constant 8) (increment numVars)) (constant 3)) d)

def bound (d n : ℕ) : ℕ := d.factorial*(8*(n+1)+3)^d

def period (d n : ℕ) : ℕ := 2^(Nat.log2 (bound d n)+1)

def coordinateCount (d n : ℕ) := (period d n)^d

def vertexCount (d n : ℕ) := (n+1)*2*coordinateCount d n

def edgeCount (d n m : ℕ) := coordinateCount d n*(m*2)

def atomCount (d n : ℕ) := n*2*vertexCount d n+1

def ruleCount (d n m : ℕ) := 3*n+2*n*edgeCount d n m+m

def occurrenceCount (d n m : ℕ) := 2*n+2*n*edgeCount d n m

def size (d n m : ℕ) := atomCount d n+ruleCount d n m+occurrenceCount d n m+1

def length (d n m : ℕ) := 4+ruleCount d n m+2*occurrenceCount d n m

def arena (d n m : ℕ) :=
  4*(Raw.recordSize d+1)*(size d n m+bound d n+coordinateCount d n+n+3*m+4)^27

def prepare (d : ℕ) : List Statement :=
  [⟨6,.load (constant 1)⟩,⟨7,.load (constant 2)⟩,
   ⟨4,constant 1⟩,⟨8,constant 1⟩,⟨9,increment (determinant d)⟩,⟨0,constant 2⟩]

def finish (d : ℕ) : List Statement :=
  [⟨9,power Cells.period d⟩,
   ⟨10,mul (two (increment numVars)) coordinates⟩,
   ⟨11,mul coordinates (two clauses)⟩,
   ⟨12,increment (mul (two numVars) vertices)⟩,
   ⟨13,add (add (three numVars) (mul (two numVars) edges)) clauses⟩,
   ⟨14,add (two numVars) (mul (two numVars) edges)⟩,
   ⟨15,increment (add (add atoms rules) occurrences)⟩,
   ⟨2,add (add (constant 4) rules) (two occurrences)⟩,
   ⟨16,input 2⟩,
   ⟨5,mul (constant (4*(Raw.recordSize d+1)))
     (power (add (add (add (add (add (input 15) (determinant d)) coordinates) numVars)
       (three clauses)) (constant 4)) 27)⟩,
   ⟨1,constant 0⟩,⟨3,constant 0⟩,⟨4,constant 1⟩]

@[simp] theorem determinant_eval (d : ℕ) (env : Env) (memory : ℕ → ℤ) (n : ℕ)
    (vars : env 6=n) : (determinant d).eval env memory=bound d n := by
  simp [determinant,bound,Cells.mul,Cells.add,Cells.constant,Cells.increment,Cells.input,Expr.eval,
    ComplexityAbstract.RAM.Arithmetic.eval,vars]

theorem bound_positive (d n : ℕ) : 0<bound d n := by
  apply Nat.mul_pos (Nat.factorial_pos d)
  exact pow_pos (by omega) _

theorem period_eq (d n : ℕ) : period d n=PeriodicTwoSAT.period (Fin (n+1)) d := by
  simp [period,bound,PeriodicTwoSAT.period,PeriodicLatticeGraph.implicationPeriod,
    PeriodicLatticeGraph.determinantBound,ImplicationGraph.coverPeriod,PeriodicTwoSAT.Signed,
    Nat.log2_eq_log_two]
  congr 3 <;> ring

/-- The header size is independent of all scratch-register contents. -/
def capacity (d : ℕ) : ℕ :=
  ((prepare d++finish d).map (fun a => a.expression.nodes)).sum+1

theorem capacity_positive (d : ℕ) : 0<capacity d := by unfold capacity; omega

theorem statement_small (d : ℕ) (a : Statement) (member : a∈prepare d++finish d) :
    a.expression.nodes≤capacity d := by
  have general (xs : List Statement) : ∀ a∈xs, a.expression.nodes≤(xs.map (fun b => b.expression.nodes)).sum := by
    induction xs with
    | nil => simp
    | cons b rest ih =>
      intro a ha
      rcases List.mem_cons.mp ha with equal | inside
      · subst a; simp
      · have h := ih a inside
        simp only [List.map_cons,List.sum_cons]
        omega
  exact (general _ a member).trans (Nat.le_succ _)

def environment (d n m : ℕ) : Env :=
  ![2,0,length d n m,0,1,arena d n m,n,m,period d n,coordinateCount d n,
    vertexCount d n,edgeCount d n m,atomCount d n,ruleCount d n m,
    occurrenceCount d n m,size d n m,length d n m]

theorem prepare_values (d n m : ℕ) (env : Env) (memory : ℕ → ℤ)
    (numVars : memory 1=n) (clauses : memory 2=m) :
    let result := Assignment.evaluate (prepare d) env memory
    result 0=2 ∧ result 8=1 ∧ result 9=bound d n+1 ∧ result 6=n ∧ result 7=m := by
  simp [prepare,Assignment.evaluate,Assignment.update,Expr.eval,Cells.constant,Cells.input,
    Cells.increment,Cells.add,ComplexityAbstract.RAM.Arithmetic.eval,Function.update_apply,
    numVars,clauses,determinant_eval]

def doubledEnvironment (d n : ℕ) (env : Env) (memory : ℕ → ℤ) : Env :=
  Function.update (Assignment.evaluate (prepare d) env memory) 8 (period d n : ℕ)

def cost (d n : ℕ) : ℕ :=
  Assignment.cost (prepare d)+(3*(Nat.log2 (bound d n)+1)+2)+Assignment.cost (finish d)

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
