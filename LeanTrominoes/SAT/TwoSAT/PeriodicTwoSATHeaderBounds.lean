/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderExpressions
import LeanTrominoes.Computation.Compiler.FiniteTwoSATPureAssignments
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Polynomial intermediate-value bounds for the 2SAT header -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM

@[simp] theorem power_pure (e : Cells.Expression) (pure : e.Pure) (n : ℕ) : (power e n).Pure := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,pure⟩

@[simp] theorem determinant_pure (d : ℕ) : (determinant d).Pure := by
  simp [determinant,Cells.mul,Cells.add,Cells.increment,Cells.constant,Cells.input,Expr.Pure,power_pure]

def prepareArithmetic (d : ℕ) : List Statement := (prepare d).drop 2

theorem prepareArithmetic_pure (d : ℕ) : ∀ a∈prepareArithmetic d, a.expression.Pure := by
  simp [prepareArithmetic,prepare,Expr.Pure,Cells.increment,Cells.add,Cells.constant,determinant_pure]

theorem finish_pure (d : ℕ) : ∀ a∈finish d, a.expression.Pure := by
  simp [finish,Cells.increment,Cells.two,Cells.three,Cells.add,Cells.mul,Cells.constant,Cells.input,
    Expr.Pure,power_pure,determinant_pure]

def constants (d : ℕ) : ℕ :=
  ((prepare d++finish d).map (fun a => a.expression.constants)).sum+2

def base (d n m : ℕ) : ℕ := constants d+n+m+bound d n+period d n+4

def exponent (d : ℕ) : ℕ :=
  Assignment.exponent (prepareArithmetic d)+Assignment.exponent (finish d)+2

theorem base_positive (d n m : ℕ) : 2≤base d n m := by unfold base; omega

theorem constants_bound (d n m : ℕ) (a : Statement) (member : a∈prepare d++finish d) :
    a.expression.constants≤base d n m := by
  have general (xs : List Statement) : ∀ a∈xs, a.expression.constants≤(xs.map (fun b => b.expression.constants)).sum := by
    induction xs with
    | nil => simp
    | cons b rest ih =>
      intro a ha
      rcases List.mem_cons.mp ha with equal | inside
      · subst a; simp
      · have h := ih a inside
        simp only [List.map_cons,List.sum_cons]
        omega
  have h := general _ a member
  dsimp [base,constants]
  omega

def preparedEnvironment (d n m : ℕ) : Env :=
  ![2,0,0,0,1,0,n,m,1,bound d n+1,0,0,0,0,0,0,0]

theorem prepare_environment (d n m : ℕ) (memory : ℕ → ℤ) (vars : memory 1=n) (clauses : memory 2=m) :
    Assignment.evaluate (prepare d) (fun _ => 0) memory=preparedEnvironment d n m := by
  funext i
  fin_cases i <;>
    simp [prepare,Assignment.evaluate,Assignment.update,preparedEnvironment,Cells.constant,Cells.increment,
      Cells.add,Cells.input,Expr.eval,Arithmetic.eval,vars,clauses,determinant_eval]

theorem prepared_bound (d n m : ℕ) : ∀ i, (preparedEnvironment d n m i).natAbs≤base d n m := by
  intro i
  fin_cases i <;> simp [preparedEnvironment,base] <;> omega

theorem doubled_bound (d n m : ℕ) (memory : ℕ → ℤ) (vars : memory 1=n) (clauses : memory 2=m) :
    ∀ i, (doubledEnvironment d n (fun _ => 0) memory i).natAbs≤base d n m := by
  rw [doubledEnvironment,prepare_environment d n m memory vars clauses]
  intro i
  simp only [Function.update_apply]
  split_ifs
  · simp only [Int.natAbs_natCast]
    unfold base
    omega
  · exact prepared_bound d n m i

/-- A uniform polynomial bound on the header's base, including its period. -/
theorem base_polynomial (d n m : ℕ) :
    base d n m≤(constants d+3*(d.factorial*11^d)+10)*(n+m+2)^(d+1) := by
  let s := n+m+2
  let A := d.factorial*11^d
  have positive : 1≤s := by dsimp [s]; omega
  have inner : 8*(n+1)+3≤11*s := by dsimp [s]; omega
  have determinant : bound d n≤A*s^d := by
    have h := Nat.mul_le_mul_left d.factorial (Nat.pow_le_pow_left inner d)
    simpa [bound,A,mul_pow,Nat.mul_assoc] using h
  have periodBound : period d n≤2*(bound d n+1) := by
    simpa only [period,ImplicationGraph.coverPeriod,← Nat.log2_eq_log_two] using
      ImplicationGraph.coverPeriod_le (bound d n)
  have high : s^d≤s^(d+1) := Nat.pow_le_pow_right positive (by omega)
  have one : s≤s^(d+1) := by simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1≤d+1 by omega)
  have nonzero : 1≤s^(d+1) := Nat.one_le_pow _ _ positive
  have determinantHigh := determinant.trans (Nat.mul_le_mul_left A high)
  change base d n m≤(constants d+3*A+10)*s^(d+1)
  unfold base
  have counts : n+m≤s := by dsimp [s]; omega
  have constantHigh : constants d≤constants d*s^(d+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (constants d) nonzero
  nlinarith

theorem base_word {d n m w : ℕ} (word : Fits w (base d n m^exponent d : ℕ)) :
    Fits w (base d n m : ℕ) := by
  apply Allocation.nat_fits_le word
  have positive := base_positive d n m
  have power : 1≤exponent d := by unfold exponent; omega
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤base d n m) power

private theorem empty_fits {w : ℕ} (zero : Fits w 0) : InputFits w [] := by
  exact ⟨by simpa using zero,by simp⟩

theorem prepare_safe {d n m w : ℕ} (memory : ℕ → ℤ)
    (vars : memory 1=n) (clauses : memory 2=m)
    (word : Fits w (base d n m^exponent d : ℕ)) :
    Assignment.Safe w 0 (prepare d) (fun _ => 0) memory := by
  have b := base_word word
  have positive := base_positive d n m
  have zero : Fits w 0 := by simpa using Allocation.nat_fits_le (a:=0) b (by omega)
  have one : Fits w 1 := by simpa using Allocation.nat_fits_le (a:=1) b (by omega)
  have two : Fits w 2 := by simpa using Allocation.nat_fits_le (a:=2) b positive
  have nword : Fits w (n : ℕ) := Allocation.nat_fits_le b (by unfold base; omega)
  have mword : Fits w (m : ℕ) := Allocation.nat_fits_le b (by unfold base; omega)
  let loaded : Env := Function.update (Function.update (fun _ => 0) 6 (n : ℕ)) 7 (m : ℕ)
  have registers : ∀ i, (loaded i).natAbs≤base d n m := by
    intro i
    simp only [loaded,Function.update_apply]
    split_ifs <;> simp only [Int.natAbs_natCast,Int.natAbs_zero] <;> unfold base <;> omega
  have arithmeticWord : Fits w (base d n m^Assignment.exponent (prepareArithmetic d) : ℕ) :=
    Allocation.nat_fits_le word (Nat.pow_le_pow_right (by omega) (by unfold exponent; omega))
  have arithmetic := Assignment.pure_safe (prepareArithmetic d) 0 loaded memory [] positive
    (prepareArithmetic_pure d)
    (by
      intro a ha
      apply constants_bound d n m a
      have h : a∈prepare d := List.mem_of_mem_drop ha
      exact List.mem_append_left _ h)
    registers arithmeticWord (empty_fits zero)
  change (Expr.load (.constant 1) : Expr 17).Safe w (fun _ => 0) memory ∧
    (Expr.load (.constant 2) : Expr 17).Safe w
      (Function.update (fun _ => 0) 6 (memory 1)) memory ∧
    Assignment.Safe w 0 (prepareArithmetic d)
      (Function.update (Function.update (fun _ => 0) 6 (memory 1)) 7 (memory 2)) memory
  rw [vars,clauses]
  refine ⟨?_,?_,arithmetic⟩
  · exact ⟨one,by norm_num [Expr.eval],by simpa [Expr.eval] using Allocation.nat_address one,by simpa [Expr.eval,vars] using nword⟩
  · exact ⟨two,by norm_num [Expr.eval],by simpa [Expr.eval] using Allocation.nat_address two,by simpa [Expr.eval,clauses] using mword⟩

theorem finish_safe {d n m w : ℕ} (memory : ℕ → ℤ)
    (vars : memory 1=n) (clauses : memory 2=m)
    (word : Fits w (base d n m^exponent d : ℕ)) :
    Assignment.Safe w 0 (finish d) (doubledEnvironment d n (fun _ => 0) memory) memory := by
  have b := base_word word
  have zero : Fits w 0 := by simpa using Allocation.nat_fits_le (a:=0) b (Nat.zero_le _)
  apply Assignment.pure_safe (finish d) 0 _ memory [] (base_positive d n m) (finish_pure d)
    (by intro a ha; exact constants_bound d n m a (List.mem_append_right _ ha))
    (doubled_bound d n m memory vars clauses) _ (empty_fits zero)
  exact Allocation.nat_fits_le word
    (Nat.pow_le_pow_right (by have := base_positive d n m; omega) (by unfold exponent; omega))


/-- One explicit polynomial base dominates every parameter used by the cell
expression, including the high source arena. -/
def tableBase (d n m : ℕ) :=
  arena d n m+size d n m+length d n m+coordinateCount d n+vertexCount d n+
    edgeCount d n m+atomCount d n+ruleCount d n m+occurrenceCount d n m+
    n+m+period d n+Raw.recordSize d+2


end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
