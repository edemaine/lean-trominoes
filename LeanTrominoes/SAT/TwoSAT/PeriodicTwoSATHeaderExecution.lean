/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderBounds
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderEvaluation

/-! # Actual execution of the periodic 2SAT constructor header -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM

variable {w c : ℕ}

def program (d c : ℕ) (positive : 0<c) : Structured.Code (17+c) :=
  .seq (Assignment.sequence c positive 0 (prepare d))
    (.seq (doublingProgram (Assignment.inputRegister c 8) (Assignment.inputRegister c 9)
      (Assignment.inputRegister c 0)) (Assignment.sequence c positive 0 (finish d)))

theorem program_exec (d n m : ℕ) (positive : 0<c) (capacity : Header.capacity d≤c)
    (data : Data (17+c)) (env : Env)
    (inputs : ∀ i, data.1 (Assignment.inputRegister c i)=env i)
    (numVars : data.2 1=n) (clauses : data.2 2=m)
    (prepareSafe : Assignment.Safe w 0 (prepare d) env data.2)
    (finishSafe : Assignment.Safe w 0 (finish d) (doubledEnvironment d n env data.2) data.2)
    (word : Fits w (period d n : ℕ)) :
    ∃ result, Structured.Exec w (program d c positive) data result (cost d n) ∧
      result.2=data.2 ∧ ∀ i, result.1 (Assignment.inputRegister c i)=environment d n m i := by
  obtain ⟨prepared,prepareRun,prepareMemory,prepareRegisters⟩ := Assignment.sequence_exec
    (prepare d) positive (by
      intro a ha
      exact (statement_small d a (by simp [ha])).trans capacity) 0 env data inputs prepareSafe
  have values := prepare_values d n m env data.2 numVars clauses
  let doubled : Data (17+c) :=
    (Function.update prepared.1 (Assignment.inputRegister c 8) (period d n : ℕ),prepared.2)
  have doubleRun := nextPower_exec (Assignment.inputRegister c 8) (Assignment.inputRegister c 9)
    (Assignment.inputRegister c 0) prepared (bound d n) (bound_positive d n)
    (by rw [prepareRegisters]; exact values.2.1)
    (by rw [prepareRegisters]; exact values.2.2.1)
    (by rw [prepareRegisters]; exact values.1)
    (by intro equal; have values := congrArg Fin.val equal; norm_num [Assignment.inputRegister] at values)
    (by intro equal; have values := congrArg Fin.val equal; norm_num [Assignment.inputRegister] at values) word
  have doubledRegisters : ∀ i, doubled.1 (Assignment.inputRegister c i)=
      doubledEnvironment d n env data.2 i := by
    intro i
    simp only [doubled,doubledEnvironment,Function.update_apply]
    by_cases same : i=8
    · subst i; simp
    · have different : Assignment.inputRegister c i≠Assignment.inputRegister c (8 : Fin 17) := by
        intro h
        apply same
        have values := congrArg (fun j : Fin (17+c) => j.val) h
        exact Fin.ext values
      rw [ite_eq_right different,ite_eq_right same,prepareRegisters]
  obtain ⟨result,finishRun,finishMemory,finishRegisters⟩ := Assignment.sequence_exec
    (finish d) positive (by
      intro a ha
      exact (statement_small d a (by simp [ha])).trans capacity) 0
    (doubledEnvironment d n env data.2) doubled doubledRegisters
    (by simpa only [doubled,prepareMemory] using finishSafe)
  have finalValues : Assignment.evaluate (finish d) (doubledEnvironment d n env data.2) data.2=
      environment d n m := by
    apply finish_values
    · simpa only [doubledEnvironment,Function.update_of_ne (by decide : (6 : Fin 17)≠8)] using values.2.2.2.1
    · simpa only [doubledEnvironment,Function.update_of_ne (by decide : (7 : Fin 17)≠8)] using values.2.2.2.2
    · simp [doubledEnvironment]
    · simpa only [doubledEnvironment,Function.update_of_ne (by decide : (0 : Fin 17)≠8)] using values.1
  refine ⟨result,?_,finishMemory.trans prepareMemory,?_⟩
  · have execution := prepareRun.seq (doubleRun.seq finishRun)
    simpa only [program,cost,Nat.add_assoc] using execution
  · intro i
    rw [finishRegisters]
    simpa only [doubled,prepareMemory] using congrFun finalValues i


end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
