/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMOriginalInput

/-! # The original-input header and the empty representative branch -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM Binary

noncomputable def headerWrap (positive : Structured.Code 128) (output : Fin 128) : Structured.Code 128 :=
  .seq GlobalPrepare128.header (.branch (.eq 66 86) (.atom (.constant output 1)) positive)

theorem headerWrap_exec {n d w bound : ℕ} (B : BasisData n d) (valid : B.Valid)
    (positive : Structured.Code 128) (output : Fin 128)
    (resourceWord : Fits w (GlobalPrepare128.resourceBound B)) (unitWord : Fits w 1)
    (runPositive : 0<n → ∃ result : Data 128, ∃ steps,
      Structured.Exec w positive (GlobalPrepare128.headerState (initialData 128 B)).word result steps ∧
      steps≤bound ∧ Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
      (result.1 output=1 ↔ Tileable (B.chart valid).region)) :
    ∃ result : Data 128, ∃ steps,
      Structured.Exec w (headerWrap positive output) (initial (r:=128) (words B)).data result steps ∧
      steps+1≤bound+11 ∧ Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
      (result.1 output=1 ↔ Tileable (B.chart valid).region) := by
  have headerRun := GlobalPrepare128.header_exec B resourceWord
  have controls := GlobalPrepare128.header_controls B
  have zero : (GlobalPrepare128.headerState (initialData 128 B)).1 (86 : Fin 128)=0 := by rfl
  by_cases empty : n=0
  · subst n
    let ready := GlobalPrepare128.headerState (initialData 128 B)
    let result := ready.set output 1
    have yes : (Structured.Condition.eq (66 : Fin 128) 86).Holds ready.word := by
      change (ready.1 (66 : Fin 128) : ℤ)=(ready.1 (86 : Fin 128) : ℤ)
      have count : ready.1 (66 : Fin 128)=0 := controls.1
      rw [count,zero]
    have answerRun := NaturalData.constant_exec ready output 1 unitWord
    have branchRun := Structured.Exec.branch_yes (no:=positive) yes answerRun
    have complete := headerRun.seq branchRun
    rw [initialData_word] at complete
    refine ⟨result.word,10,complete,by omega,?_,?_,?_⟩
    · simpa [result,NaturalData.word,NaturalData.set] using unitWord
    · right; simp [result,NaturalData.word,NaturalData.set]
    · exact iff_of_true (by simp [result,NaturalData.word,NaturalData.set]) (empty_tileable B valid)
  · obtain ⟨result,steps,run,budget,fits,boolean,correct⟩ := runPositive (by omega)
    have no : ¬(Structured.Condition.eq (66 : Fin 128) 86).Holds (GlobalPrepare128.headerState (initialData 128 B)).word := by
      change ¬((GlobalPrepare128.headerState (initialData 128 B)).1 (66 : Fin 128) : ℤ)=((GlobalPrepare128.headerState (initialData 128 B)).1 (86 : Fin 128) : ℤ)
      rw [controls.1,zero]
      exact_mod_cast empty
    have branchRun := Structured.Exec.branch_no (yes:=.atom (.constant output 1)) no run
    have complete := headerRun.seq branchRun
    rw [initialData_word] at complete
    exact ⟨result,8+(steps+2),complete,by omega,fits,boolean,correct⟩

end LeanTrominoes.Domino.WordRAM
