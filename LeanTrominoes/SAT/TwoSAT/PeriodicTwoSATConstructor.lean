/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCopyExecution
import LeanTrominoes.Computation.Compiler.FiniteTwoSATInvocation

/-! # End-to-end execution after the original-input arithmetic header -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d c w : ℕ}

def constructorProgram (d c : ℕ) (positive : 0<c) (copyBank : 21 ≤ 17+c)
    (tableBank : registerCount d ≤ 17+c) (hornBank : 32 ≤ 17+c) : Structured.Code (17+c) :=
  .seq (copyOriginalProgram d c positive copyBank)
    (.seq ((tableProgram d).widen tableBank) (coldInvokeHorn.widen hornBank))

theorem constructor_exec (raw : Raw.LocalInput d) (arena base : ℕ) (positive : 0<c) (capacity : 2≤c)
    (copyBank : 21 ≤ 17+c) (tableBank : registerCount d ≤ 17+c) (hornBank : 32 ≤ 17+c)
    (data : Data (17+c))
    (index : data.1 (callerReg c 1)=0) (length : data.1 (callerReg c 2)=(fullWords raw.val).length)
    (unit : data.1 (callerReg c 4)=1) (sourceValue : data.1 (callerReg c 5)=arena)
    (savedLength : data.1 (callerReg c 16)=(fullWords raw.val).length)
    (header : Metadata raw.val (tablePeriod raw.val) (fun i => data.1 (callerReg c i)))
    (lengthHeader : data.2 0=(Raw.words raw.val).length)
    (inputMemory : InputAt (Raw.words raw.val) data.2)
    (separate : (Raw.words raw.val).length < arena) (sourceHigh : (fullWords raw.val).length ≤ arena)
    (parameterBounds : ∀ i : Fin 17, 5 ≤ i.val → (data.1 (callerReg c i)).natAbs ≤ base)
    (recordSize : Raw.recordSize d ≤ base) (variableBound : raw.val.1+1 ≤ base)
    (lengthBound : (fullWords raw.val).length ≤ base) (oneBound : 1 ≤ base)
    (inputFits : InputFits w (Raw.words raw.val))
    (arenaFits : Fits w (arena+(Raw.words raw.val).length : ℕ))
    (lengthFits : Fits w (fullWords raw.val).length) (oneFits : Fits w 1)
    (budgetFits : Fits w (base^(2*(cell d).nodes)))
    (width : hornWidth (uniformInput raw.val.2) ≤ w)
    (hornArena : 2^hornWidth (uniformInput raw.val.2) ≤ arena) :
    ∃ result, ∃ steps, Structured.Exec w (constructorProgram d c positive copyBank tableBank hornBank) data result steps ∧
      steps+1 ≤ 9*(Raw.words raw.val).length+((cell d).nodes+5)*(fullWords raw.val).length+
        4*arena+55+120*(Horn.WordRAM.size (uniformInput raw.val.2)+1) ∧
      Fits w (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)) ∧
      (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=0 ∨
        result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1) ∧
      (result.1 (Fin.castLE hornBank Horn.WordRAM.Reg.output)=1 ↔ Satisfiable raw.val.2) := by
  obtain ⟨copied,copyRun,copyIndex,copyLength,copyBase,copyUnit,copySource,copyParameters⟩ :=
    copyOriginal_exec raw.val arena positive capacity copyBank data index unit sourceValue savedLength
      lengthHeader inputMemory separate inputFits arenaFits lengthFits oneFits
  let small := copied.restrict tableBank
  have controls : Table.Controls (k:=12) (cell d) small 0 (fullWords raw.val).length 0 :=
    ⟨copyIndex,copyLength,copyBase,copyUnit⟩
  have copiedHeader : Metadata raw.val (tablePeriod raw.val) (fun i => small.1 (inputRegister d i)) := by
    apply header.congr
    · exact copyLength.trans length.symm
    · exact copyParameters
  have copiedBounds (i : Fin 17) (hi : 5 ≤ i.val) : (small.1 (inputRegister d i)).natAbs ≤ base := by
    change (copied.1 (callerReg c i)).natAbs ≤ base
    rw [copyParameters i hi]
    exact parameterBounds i hi
  obtain ⟨tabled,tableRun,tableControls,tableMemory,tableParameters⟩ := table_exec raw arena base w small
    controls copySource ((copyParameters 5 (by decide)).trans sourceValue) copiedHeader sourceHigh copiedBounds
    recordSize variableBound lengthBound oneBound lengthFits budgetFits inputFits
  obtain ⟨largeTabled,largeTableRun,largeTableMemory,largeTableRegisters,_⟩ := tableRun.widen_restrict tableBank
  have tabledRegisters (i : Fin 17) : largeTabled.1 (callerReg c i)=tabled.1 (inputRegister d i) :=
    widened_input tableBank tabled largeTabled largeTableRegisters i
  let cold : Data 32 := largeTabled.restrict hornBank
  have coldIndex : cold.1 1=(fullWords raw.val).length := by
    change largeTabled.1 (callerReg c 1)=(fullWords raw.val).length
    rw [tabledRegisters]
    exact tableControls.1
  have coldLength : cold.1 2=(fullWords raw.val).length := by
    change largeTabled.1 (callerReg c 2)=(fullWords raw.val).length
    rw [tabledRegisters]
    exact tableControls.2.1
  have coldArena : cold.1 5=arena := by
    change largeTabled.1 (callerReg c 5)=arena
    rw [tabledRegisters,tableParameters _ (by decide)]
    change copied.1 (callerReg c 5)=arena
    rw [copyParameters _ (by decide)]
    exact sourceValue
  have coldTable (a : ℕ) (inside : a < (fullWords raw.val).length) :
      cold.2 a=(initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.val.2))).data.2 a := by
    change largeTabled.2 a=_
    rw [largeTableMemory,tableMemory]
    simp only [prefixMemory,Nat.zero_le,zero_add,Nat.sub_zero,true_and,inside,ite_true]
    rfl
  have coldZero (a : ℕ) (outside : (fullWords raw.val).length ≤ a) :
      (initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.val.2))).data.2 a=0 := by
    rw [show (initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.val.2))).data.2 a=
      ((fullWords raw.val)[a]?.getD 0 : ℕ) from fullWords_initial raw.val a,
      List.getElem?_eq_none outside]
    rfl
  have arenaWord : Fits w arena := Allocation.nat_fits_le arenaFits (by omega)
  obtain ⟨solved,solveSteps,solveRun,solveBudget,solveFits,solveBoolean,solveCorrect,_⟩ := coldInvokeHorn_exec
    (uniformInput raw.val.2) cold coldIndex coldLength coldArena sourceHigh arenaWord oneFits width hornArena coldTable coldZero
  obtain ⟨result,resultRun,resultMemory,resultRegisters,_⟩ := solveRun.widen_restrict hornBank
  refine ⟨result,(9*(Raw.words raw.val).length+15)+(((cell d).nodes+5)*(fullWords raw.val).length+2+solveSteps),?_,?_,?_,?_,?_⟩
  · exact copyRun.seq (largeTableRun.seq resultRun)
  · omega
  · rw [resultRegisters]
    exact solveFits
  · rw [resultRegisters]
    exact solveBoolean
  · rw [resultRegisters,solveCorrect,uniformInput_correct raw.val.2 raw.property]

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
