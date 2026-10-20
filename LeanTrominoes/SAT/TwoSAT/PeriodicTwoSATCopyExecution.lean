/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATTableExecution
import LeanTrominoes.Computation.Compiler.FiniteTwoSATCopy
import LeanTrominoes.Computation.Compiler.FiniteTwoSATCopySetup
import LeanTrominoes.Computation.Compiler.FiniteTwoSATRegisters

/-! # Original clause copying with concrete setup and restoration instructions -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d c w : ℕ}

abbrev callerReg (c : ℕ) (i : Fin 17) : Fin (17+c) := Assignment.inputRegister c i
abbrev copyProgram := Table.program (k:=12) (copyExpression 12)

theorem restrict_input {c : ℕ} {e : Expr 17} (large : e.registers ≤ 17+c) (data : Data (17+c)) (i : Fin 17) :
    (data.restrict large).1 (e.inputRegister i)=data.1 (callerReg c i) := rfl

theorem widened_input {c : ℕ} {e : Expr 17} (large : e.registers ≤ 17+c)
    (small : Data e.registers) (caller : Data (17+c))
    (registers : ∀ i, caller.1 (Fin.castLE large i)=small.1 i) (i : Fin 17) :
    caller.1 (callerReg c i)=small.1 (e.inputRegister i) := registers (e.inputRegister i)

def copyOriginalProgram (d c : ℕ) (positive : 0<c) (copyBank : 21 ≤ 17+c) : Structured.Code (17+c) :=
  .seq (Assignment.sequence c positive 4 CopySetup.prepare)
    (.seq (copyProgram.widen copyBank) (Assignment.sequence c positive 4 CopySetup.resume))

theorem copyOriginal_exec (raw : Raw.Input d) (arena : ℕ) (positive : 0<c) (capacity : 2≤c)
    (copyBank : 21 ≤ 17+c) (data : Data (17+c))
    (index : data.1 (callerReg c 1)=0) (unit : data.1 (callerReg c 4)=1)
    (sourceValue : data.1 (callerReg c 5)=arena)
    (savedLength : data.1 (callerReg c 16)=(fullWords raw).length)
    (lengthHeader : data.2 0=(Raw.words raw).length)
    (inputMemory : InputAt (Raw.words raw) data.2)
    (separate : (Raw.words raw).length < arena)
    (inputFits : InputFits w (Raw.words raw))
    (arenaFits : Fits w (arena+(Raw.words raw).length : ℕ))
    (lengthFits : Fits w (fullWords raw).length) (oneFits : Fits w 1) :
    ∃ result, Structured.Exec w (copyOriginalProgram d c positive copyBank) data result
        (9*(Raw.words raw).length+15) ∧
      result.1 (callerReg c 1)=0 ∧ result.1 (callerReg c 2)=(fullWords raw).length ∧
      result.1 (callerReg c 3)=0 ∧ result.1 (callerReg c 4)=1 ∧
      Raw.SourceAt raw arena result.2 ∧
      (∀ i : Fin 17, 5≤ i.val → result.1 (callerReg c i)=data.1 (callerReg c i)) := by
  let env := fun i => data.1 (callerReg c i)
  have arenaWord : Fits w arena := Allocation.nat_fits_le arenaFits (by omega)
  obtain ⟨prepared,prepareRun,prepareMemory,prepareRegisters⟩ := Assignment.sequence_exec
    CopySetup.prepare positive (by intro a ha; exact (CopySetup.prepare_small a ha).trans capacity) 4 env data
    (fun _ => rfl) (CopySetup.prepare_safe env data.2 sourceValue unit lengthHeader arenaWord inputFits.1 oneFits)
  have prepareValues := CopySetup.prepare_values env data.2
  have preparedRegisters (i : Fin 17) : prepared.1 (callerReg c i)=
      Function.update (Function.update env 2 (data.2 0)) 3 (env 5) i := by
    rw [prepareRegisters,prepareValues]
  let small : Data 21 := prepared.restrict copyBank
  have smallControls : Table.Controls (k:=12) (copyExpression 12) small 0 (Raw.words raw).length arena := by
    refine ⟨?_,?_,?_,?_⟩
    all_goals change prepared.1 (callerReg c _) = _
    all_goals simp only [preparedRegisters,Function.update_apply,env,lengthHeader,index,sourceValue,unit]
    all_goals norm_num
  obtain ⟨copied,copyRun,copyControls,copyMemory,copyPreserved⟩ := copy_exec (k:=12) (Raw.words raw)
    small separate inputFits arenaFits smallControls (by simpa only [small,Data.restrict,prepareMemory] using inputMemory)
  obtain ⟨largeCopied,largeCopyRun,largeCopyMemory,largeCopyRegisters,_⟩ := copyRun.widen_restrict copyBank
  have copiedParameters (i : Fin 17) (parameter : 5≤ i.val) :
      largeCopied.1 (callerReg c i)=data.1 (callerReg c i) := by
    rw [widened_input copyBank copied largeCopied largeCopyRegisters i]
    change copied.1 (Table.reg (copyExpression 12) i)=data.1 (callerReg c i)
    rw [copyPreserved i parameter]
    change prepared.1 (callerReg c i)=env i
    rw [preparedRegisters]
    simp only [Function.update_apply]
    have notTwo : i ≠ 2 := by intro same; subst i; norm_num at parameter
    have notThree : i ≠ 3 := by intro same; subst i; norm_num at parameter
    rw [if_neg notThree,if_neg notTwo]
  have copiedUnit : largeCopied.1 (callerReg c 4)=1 :=
    (widened_input copyBank copied largeCopied largeCopyRegisters 4).trans copyControls.2.2.2
  let copiedEnv := fun i => largeCopied.1 (callerReg c i)
  obtain ⟨result,resumeRun,resumeMemory,resumeRegisters⟩ := Assignment.sequence_exec
    CopySetup.resume positive (by intro a ha; exact (CopySetup.resume_small a ha).trans capacity) 4 copiedEnv largeCopied
    (fun _ => rfl) (CopySetup.resume_safe copiedEnv largeCopied.2
      ((copiedParameters 16 (by decide)).trans savedLength) copiedUnit lengthFits oneFits)
  have resumeValues := CopySetup.resume_values copiedEnv largeCopied.2
  have registers (i : Fin 17) : result.1 (callerReg c i)=
      Function.update (Function.update (Function.update copiedEnv 1 0) 2 (copiedEnv 16)) 3 0 i := by
    rw [resumeRegisters,resumeValues]
  refine ⟨result,?_,?_,?_,?_,?_,?_,?_⟩
  · have run := prepareRun.seq (largeCopyRun.seq resumeRun)
    have total : Assignment.cost CopySetup.prepare+((9*(Raw.words raw).length+2)+Assignment.cost CopySetup.resume)=9*(Raw.words raw).length+15 := by
      rw [CopySetup.prepare_cost,CopySetup.resume_cost]
      omega
    simpa only [copyOriginalProgram,copyProgram,total] using run
  · simp [registers]
  · simpa [registers,copiedEnv] using (copiedParameters 16 (by decide)).trans savedLength
  · simp [registers]
  · simpa [registers,copiedEnv] using copiedUnit
  · intro i inside
    rw [resumeMemory,largeCopyMemory,copyMemory]
    simp only [prefixMemory,Nat.le_add_right,Nat.add_lt_add_iff_left,inside,and_self,ite_true,Nat.add_sub_cancel_left]
  · intro i parameter
    rw [registers]
    have notOne : i ≠ 1 := by intro same; subst i; norm_num at parameter
    have notTwo : i ≠ 2 := by intro same; subst i; norm_num at parameter
    have notThree : i ≠ 3 := by intro same; subst i; norm_num at parameter
    simp only [Function.update_apply,if_neg notOne,if_neg notTwo,if_neg notThree,copiedEnv]
    exact copiedParameters i parameter

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
