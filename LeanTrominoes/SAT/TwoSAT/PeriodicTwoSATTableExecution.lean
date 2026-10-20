/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellCorrectness
import LeanTrominoes.Computation.Compiler.FiniteTwoSATTable

/-! # Actual bounded-word construction of the complete dense Horn input -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d : ℕ}

abbrev registerCount (d : ℕ) := (cell d).registers
abbrev inputRegister (d : ℕ) (i : Fin 17) : Fin (registerCount d) := Table.reg (k:=12) (cell d) i
abbrev tableProgram (d : ℕ) := Table.program (k:=12) (cell d)

theorem Metadata.congr {raw : Raw.Input d} {M : ℕ} {env current : Fin 17 → ℤ}
    (header : Metadata raw M env) (length : current 2 = env 2)
    (parameters : ∀ i, 5 ≤ i.val → current i = env i) : Metadata raw M current := by
  exact ⟨(parameters 6 (by decide)).trans header.numVars,
    (parameters 7 (by decide)).trans header.clauses,
    (parameters 8 (by decide)).trans header.period,
    (parameters 9 (by decide)).trans header.coordinates,
    (parameters 10 (by decide)).trans header.vertices,
    (parameters 11 (by decide)).trans header.edges,
    (parameters 12 (by decide)).trans header.atoms,
    (parameters 13 (by decide)).trans header.rules,
    (parameters 14 (by decide)).trans header.occurrences,length.trans header.length⟩

/-- The loop builds the exact Horn input from preserved original records.
Its bound counts the primitive expression instructions at every generated word. -/
theorem table_exec (raw : Raw.LocalInput d) (sourceBase base w : ℕ)
    (data : Data (registerCount d))
    (controls : Table.Controls (k:=12) (cell d) data 0 (fullWords raw.val).length 0)
    (source : Raw.SourceAt raw.val sourceBase data.2)
    (baseValue : data.1 (inputRegister d 5) = sourceBase)
    (header : Metadata raw.val (tablePeriod raw.val) (fun i => data.1 (inputRegister d i)))
    (sourceHigh : (fullWords raw.val).length ≤ sourceBase)
    (parameterBounds : ∀ i : Fin 17, 5 ≤ i.val → (data.1 (inputRegister d i)).natAbs ≤ base)
    (recordSize : Raw.recordSize d ≤ base) (variableBound : raw.val.1+1 ≤ base)
    (lengthBound : (fullWords raw.val).length ≤ base) (oneBound : 1 ≤ base)
    (lengthFits : Fits w (fullWords raw.val).length)
    (budgetFits : Fits w (base^(2*(cell d).nodes)))
    (inputFits : InputFits w (Raw.words raw.val)) :
    ∃ result, Structured.Exec w (tableProgram d) data result
        (((cell d).nodes+5)*(fullWords raw.val).length+2) ∧
      Table.Controls (k:=12) (cell d) result (fullWords raw.val).length (fullWords raw.val).length 0 ∧
      result.2 = prefixMemory data.2 0
        ((initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.val.2))).memory)
        (fullWords raw.val).length ∧
      ∀ i : Fin 17, 5 ≤ i.val → result.1 (inputRegister d i)=data.1 (inputRegister d i) := by
  let values : ℕ → ℤ := (initial (r:=32) (Horn.WordRAM.encode (uniformInput raw.val.2))).memory
  have contract : ∀ i, i < (fullWords raw.val).length → ∀ current : Data (registerCount d),
      Table.Controls (k:=12) (cell d) current i (fullWords raw.val).length 0 →
      current.2 = prefixMemory data.2 0 values i →
      (∀ j : Fin 17, 5 ≤ j.val → current.1 (inputRegister d j)=data.1 (inputRegister d j)) →
      (cell d).Safe w (fun j => current.1 (inputRegister d j)) current.2 ∧
        (cell d).eval (fun j => current.1 (inputRegister d j)) current.2=values i ∧ Fits w (values i) := by
    intro i inside current currentControls currentMemory parameters
    have currentSource : Raw.SourceAt raw.val sourceBase current.2 := by
      intro j hj
      rw [currentMemory]
      simp only [prefixMemory,Nat.zero_le,zero_add,Nat.sub_zero,true_and]
      rw [if_neg (by omega : ¬sourceBase+j < i)]
      exact source j hj
    have currentBase : current.1 (inputRegister d 5) = sourceBase := by rw [parameters _ (by decide)]; exact baseValue
    have currentHeader : Metadata raw.val (tablePeriod raw.val) (fun j => current.1 (inputRegister d j)) := by
      apply header.congr (parameters:=parameters)
      exact currentControls.2.1.trans controls.2.1.symm
    have currentBounds : ∀ j : Fin 17, j ≠ 0 → (current.1 (inputRegister d j)).natAbs ≤ base := by
      intro j nonzero
      by_cases parameter : 5 ≤ j.val
      · rw [parameters j parameter]
        exact parameterBounds j parameter
      · have alternatives : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by
          have nonzeroVal : j.val ≠ 0 := by intro zero; exact nonzero (Fin.ext zero)
          have val : j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 := by omega
          simpa [Fin.ext_iff] using val
        rcases alternatives with rfl | rfl | rfl | rfl
        · simpa only [currentControls.1,Int.natAbs_natCast] using (Nat.le_of_lt inside).trans lengthBound
        · simpa only [currentControls.2.1,Int.natAbs_natCast] using lengthBound
        · simpa only [currentControls.2.2.1,Int.natAbs_natCast] using (Nat.zero_le base)
        · simpa only [currentControls.2.2.2,Int.natAbs_one] using oneBound
    let context : Context base raw sourceBase (fun j => current.1 (inputRegister d j)) current.2 :=
      ⟨currentSource,currentBase,currentHeader.clauses,currentBounds,recordSize,variableBound⟩
    have safe := context.cellBounded.safe w budgetFits inputFits
    have value : (cell d).eval (fun j => current.1 (inputRegister d j)) current.2 = values i := by
      rw [show values i = ((fullWords raw.val)[i]?.getD 0 : ℕ) from fullWords_initial raw.val i]
      exact cell_eval raw.val sourceBase _ _ currentSource currentBase currentHeader i inside currentControls.1
    refine ⟨safe,value,?_⟩
    rw [← value]
    exact Expr.safe_result _ _ _ safe
  have addressFits : ∀ i, i < (fullWords raw.val).length → Fits w (0+i : ℕ) := by
    intro i hi
    simpa only [Nat.zero_add] using Allocation.nat_fits_le lengthFits (Nat.le_of_lt hi)
  have nextFits : ∀ i, i < (fullWords raw.val).length → Fits w (i+1 : ℕ) := by
    intro i hi
    exact Allocation.nat_fits_le lengthFits (by omega)
  exact Table.loop_exec (k:=12) (cell d) data.2 values (fun j => data.1 (inputRegister d j))
    addressFits nextFits contract (fullWords raw.val).length 0 (by omega) data controls
    (by simpa only [prefixMemory_zero]) (fun _ _ => rfl)

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
