/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATConstructor
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATConstructorBounds
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderExecution
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderGeometry

/-! # Polynomial-time bounded-word RAM for periodic local 2SAT

At each fixed dimension one fixed program reads the original signed clause
records, computes its period and finite-cover sizes, copies the records to a
high arena, generates the complete implication batches, and runs Horn SAT.
All arithmetic, copying, table generation, clearing, and halt instructions
are counted. Every word size above a constant multiple of log(input size)
is supported, subject to the ordinary input-word representability condition.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open ImplicationGraph ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM

variable {d : ℕ}

def scratch (d : ℕ) : ℕ := Header.capacity d+(Cells.cell d).nodes+32

theorem scratch_positive (d : ℕ) : 0 < scratch d := by unfold scratch; omega

theorem scratch_header (d : ℕ) : Header.capacity d ≤ scratch d := by unfold scratch; omega

theorem scratch_copy (d : ℕ) : 21 ≤ 17+scratch d := by unfold scratch; omega

theorem scratch_table (d : ℕ) : Cells.registerCount d ≤ 17+scratch d := by
  dsimp [Cells.registerCount,Expr.registers,scratch]
  omega

theorem scratch_horn (d : ℕ) : 32 ≤ 17+scratch d := by unfold scratch; omega

def programWithBank (d c : ℕ) (positive : 0<c) (copyBank : 21 ≤ 17+c)
    (tableBank : Cells.registerCount d ≤ 17+c) (hornBank : 32 ≤ 17+c) : Structured.Code (17+c) :=
  .seq (Header.program d c positive)
    (Cells.constructorProgram d c positive copyBank tableBank hornBank)

def program (d : ℕ) : Structured.Code (17+scratch d) :=
  programWithBank d (scratch d) (scratch_positive d) (scratch_copy d) (scratch_table d) (scratch_horn d)

def output (d : ℕ) : Fin (17+scratch d) := Fin.castLE (scratch_horn d) Horn.WordRAM.Reg.output

/-- The original-input program executes with one shared polynomial word budget. -/
theorem program_verified_withBank (c : ℕ) (positive : 0<c) (smallBank : 2≤c)
    (headerBank : Header.capacity d ≤ c) (copyBank : 21 ≤ 17+c)
    (tableBank : Cells.registerCount d ≤ 17+c) (hornBank : 32 ≤ 17+c) (raw : Raw.LocalInput d) (w : ℕ)
    (resourceWord : Fits w (Header.resources d raw.val.1 raw.val.2.length : ℕ))
    (inputFits : InputFits w (Raw.encode raw)) :
    ∃ result : Data (17+c), ∃ steps,
      Structured.Exec w (programWithBank d c positive copyBank tableBank hornBank) (initial (r:=17+c) (Raw.encode raw)).data result steps ∧
      steps+1 ≤ Header.totalBound d raw.val.1 raw.val.2.length ∧
      Fits w (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)) ∧
      (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=0 ∨ result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1) ∧
      (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1 ↔ Raw.Satisfiable raw) := by
  let original := (initial (r:=17+c) (Raw.encode raw)).data
  have vars : original.2 1=raw.val.1 := by rfl
  have clauses : original.2 2=raw.val.2.length := by rfl
  have headerWord : Fits w (Header.base d raw.val.1 raw.val.2.length^Header.exponent d : ℕ) :=
    Allocation.nat_fits_le resourceWord (by unfold Header.resources; omega)
  have periodWord : Fits w (Header.period d raw.val.1 : ℕ) :=
    Allocation.nat_fits_le (Header.base_word headerWord) (by unfold Header.base; omega)
  obtain ⟨prepared,headerRun,headerMemory,headerRegisters⟩ := Header.program_exec
    d raw.val.1 raw.val.2.length positive headerBank original (fun _ => 0)
    (fun _ => rfl) vars clauses (Header.prepare_safe original.2 vars clauses headerWord)
    (Header.finish_safe original.2 vars clauses headerWord) periodWord
  have environment : (fun i => prepared.1 (Cells.callerReg c i))=
      Header.environment d raw.val.1 raw.val.2.length := funext headerRegisters
  have inputLength : prepared.2 0=(Raw.words raw.val).length := by
    rw [headerMemory]
    rfl
  have inputMemory : InputAt (Raw.words raw.val) prepared.2 := by
    rw [headerMemory]
    exact inputAt_initial (Raw.words raw.val)
  have lengthFits : Fits w (Cells.fullWords raw.val).length := by
    rw [← Header.length_fullWords raw.val]
    exact Allocation.nat_fits_le resourceWord (by unfold Header.resources; omega)
  have arenaFits : Fits w (Header.arena d raw.val.1 raw.val.2.length+(Raw.words raw.val).length : ℕ) := by
    rw [Raw.words_length]
    exact Allocation.nat_fits_le resourceWord (by unfold Header.resources Header.originalLength; omega)
  have arenaWord : Fits w (Header.arena d raw.val.1 raw.val.2.length : ℕ) :=
    Allocation.nat_fits_le arenaFits (by omega)
  have oneFits : Fits w 1 := Allocation.nat_fits_le (a:=1) resourceWord (by unfold Header.resources; omega)
  have budgetFits : Fits w (Header.tableBase d raw.val.1 raw.val.2.length^(2*(Cells.cell d).nodes) : ℕ) :=
    Allocation.nat_fits_le resourceWord (by unfold Header.resources; omega)
  have bounds := Header.tableBase_aux d raw.val.1 raw.val.2.length
  have lengthBound : (Cells.fullWords raw.val).length ≤ Header.tableBase d raw.val.1 raw.val.2.length := by
    rw [← Header.length_fullWords raw.val]
    exact bounds.2.2.1
  have parameters : ∀ i : Fin 17, 5 ≤ i.val →
      (prepared.1 (Cells.callerReg c i)).natAbs ≤ Header.tableBase d raw.val.1 raw.val.2.length := by
    intro i hi
    rw [headerRegisters]
    exact Header.tableBase_parameters d raw.val.1 raw.val.2.length i hi
  have metadata : Cells.Metadata raw.val (Cells.tablePeriod raw.val)
      (fun i => prepared.1 (Cells.callerReg c i)) := by
    rw [environment]
    exact Header.environment_metadata raw.val
  have index : prepared.1 (Cells.callerReg c 1)=0 := by rw [headerRegisters]; rfl
  have unit : prepared.1 (Cells.callerReg c 4)=1 := by rw [headerRegisters]; rfl
  have arena : prepared.1 (Cells.callerReg c 5)=Header.arena d raw.val.1 raw.val.2.length := by
    rw [headerRegisters]; rfl
  have length : prepared.1 (Cells.callerReg c 2)=(Cells.fullWords raw.val).length := by
    rw [headerRegisters]
    change (Header.length d raw.val.1 raw.val.2.length : ℤ) = (Cells.fullWords raw.val).length
    rw [Header.length_fullWords raw.val]
  have saved : prepared.1 (Cells.callerReg c 16)=(Cells.fullWords raw.val).length := by
    rw [headerRegisters]
    change (Header.length d raw.val.1 raw.val.2.length : ℤ) = (Cells.fullWords raw.val).length
    rw [Header.length_fullWords raw.val]
  obtain ⟨result,steps,run,budget,fits,boolean,correct⟩ := Cells.constructor_exec raw
    (Header.arena d raw.val.1 raw.val.2.length) (Header.tableBase d raw.val.1 raw.val.2.length)
    positive smallBank copyBank tableBank hornBank
    prepared index length unit arena saved metadata inputLength inputMemory (Header.rawLength_lt_arena raw.val)
    (by rw [← Header.length_fullWords raw.val]; exact Header.length_le_arena _ _ _)
    parameters bounds.1 bounds.2.1 lengthBound bounds.2.2.2 inputFits arenaFits lengthFits oneFits (by simpa only [Nat.cast_pow] using budgetFits)
    (Header.hornWidth_le_of_arena_fits raw.val arenaWord) (Header.arena_hornWidth raw.val)
  have time : Header.cost d raw.val.1+steps+1 ≤ Header.totalBound d raw.val.1 raw.val.2.length := by
    simpa only [Header.totalBound,Header.originalLength,Raw.words_length,
      Header.length_fullWords raw.val,Header.size_uniform raw.val,Nat.add_assoc]
      using Nat.add_le_add_left budget (Header.cost d raw.val.1)
  have execution : Structured.Exec w (programWithBank d c positive copyBank tableBank hornBank) original result (Header.cost d raw.val.1+steps) := by
    exact headerRun.seq run
  have outputFits : Fits w (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)) := fits
  have outputBoolean : result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=0 ∨ result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1 := boolean
  have outputCorrect : result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1 ↔ Raw.Satisfiable raw := correct
  exact ⟨result,Header.cost d raw.val.1+steps,execution,time,outputFits,outputBoolean,outputCorrect⟩


theorem program_verified (raw : Raw.LocalInput d) (w : ℕ)
    (resourceWord : Fits w (Header.resources d raw.val.1 raw.val.2.length : ℕ))
    (inputFits : InputFits w (Raw.encode raw)) :
    ∃ result : Data (17+scratch d), ∃ steps,
      Structured.Exec w (program d) (initial (r:=17+scratch d) (Raw.encode raw)).data result steps ∧
      steps+1 ≤ Header.totalBound d raw.val.1 raw.val.2.length ∧
      Fits w (result.1 (output d)) ∧
      (result.1 (output d)=0 ∨ result.1 (output d)=1) ∧
      (result.1 (output d)=1 ↔ Raw.Satisfiable raw) := by
  exact program_verified_withBank (scratch d) (scratch_positive d) (by unfold scratch; omega)
    (scratch_header d) (scratch_copy d) (scratch_table d) (scratch_horn d) raw w resourceWord inputFits

/-- At each fixed dimension the original signed-record problem has a genuine
polynomial-time word-RAM decision algorithm using logarithmic-size words. -/
theorem polynomialTime (d : ℕ) : PolynomialTime Raw.encode Raw.size (Raw.Satisfiable (d:=d)) := by
  obtain ⟨resourceCoefficient,resourceFits⟩ := Header.resource_fits d
  obtain ⟨C,exponent,timeBound⟩ := Header.totalBound_polynomial d
  let k := resourceCoefficient+Nat.log2 ((program d).size+1)
  refine ⟨C,exponent,k,?_⟩
  apply Structured.decidesWithin (program d) (output d) Raw.encode Raw.Satisfiable
  intro raw w width inputFits
  have resourceWidth : resourceCoefficient*Nat.log2 (raw.val.1+raw.val.2.length+3)+2 ≤ w := by
    have bound : resourceCoefficient*Nat.log2 (Raw.size raw+2)+2 ≤ w :=
      (Nat.add_le_add_right (Nat.mul_le_mul_right _
        (Nat.le_add_right resourceCoefficient (Nat.log2 ((program d).size+1)))) 2).trans width
    have sizeEquation : Raw.size raw+2=raw.val.1+raw.val.2.length+3 := by unfold Raw.size; omega
    rw [sizeEquation] at bound
    exact bound
  have word := resourceFits raw.val.1 raw.val.2.length w resourceWidth
  obtain ⟨result,steps,execution,time,fits,boolean,correct⟩ := program_verified raw w word inputFits
  have pcWidth : (Nat.log2 ((program d).size+1)+2*0)*Nat.log2 (Raw.size raw+2)+2 ≤ w := by
    have bound : (resourceCoefficient+Nat.log2 ((program d).size+1))*Nat.log2 (Raw.size raw+2)+2 ≤ w := width
    simpa only [Nat.mul_zero,Nat.add_zero] using
      (Nat.add_le_add_right (Nat.mul_le_mul_right _
        (Nat.le_add_left (Nat.log2 ((program d).size+1)) resourceCoefficient)) 2).trans bound
  have pcWord : Fits w ((program d).size : ℕ) := WordBounds.polynomial_fits_uniform
    (program d).size 0 (Raw.size raw) w (program d).size pcWidth (by simp only [Int.natAbs_natCast,pow_zero,Nat.mul_one]; exact Nat.le_refl _)
  have pc : (program d).size < 2^w := Int.ofNat_lt.mp (Allocation.nat_address pcWord)
  refine ⟨pc,result,steps,execution,time.trans ?_,fits,boolean,correct⟩
  simpa only [Raw.size,Nat.add_assoc] using timeBound raw.val.1 raw.val.2.length

end LeanTrominoes.PeriodicTwoSAT.WordRAM
