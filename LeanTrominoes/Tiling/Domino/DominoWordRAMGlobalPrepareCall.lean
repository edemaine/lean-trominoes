/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareFresh
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateFrame

/-! # The checked global determinant call and its persistent postcondition -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

noncomputable def determinantCall (d : Nat) : Code :=
  .seq (determinantHeaders d) ((DeterminantSetup.program d).embed 64)

noncomputable def determinantCost {n d : Nat} (B : BasisData n d) : Nat :=
  (26*WordRAM.precision B^2+26*WordRAM.precision B+16)*(DeterminantSetup.compiled d).nodes.length+29*WordRAM.precision B+42

theorem determinantCall_exec {n d w : Nat} (B : BasisData n d) (positive : 0<n) (nonzero : B.basis.det≠0)
    (data : Data) (ready : DeterminantReady B positive data) (width : Fits w (resourceBound B)) :
    ∃ result cost, NaturalData.Exec w (determinantCall d) data result cost ∧
      cost≤8+determinantCost B ∧ Candidate.Frame B ⟨0,positive⟩ ⟨0,positive⟩ result ∧
      result.1 H.n=n ∧ result.1 H.frontier=endAddress B := by
  obtain ⟨headers,controls,memory,fixed⟩ := determinantHeaders_exec B data ready.controls.base ready.controls.precision
    ready.controls.zero ready.controls.determinant ready.controls.twice width
  have prepared := ready.transport fixed memory
  have detFits : Fits (WordRAM.precision B) B.basis.det :=
    LeanTrominoes.WordBounds.fits_mono (by unfold WordRAM.precision; omega) (WordRAM.determinant_fits B)
  obtain ⟨small,cost,run,budget,correct,preserved⟩ := DeterminantSetup.determinant_exec (geometry B)
    (Lower (determinantPrepared d data)) (determinant_widths B width) controls
    (rawInputs B ⟨0,positive⟩ ⟨0,positive⟩) B.basis (rawInputs_basis B _ _) prepared.known
    (WordRAM.precision_positive B) prepared.fresh prepared.zero detFits (by have guard := WordRAM.determinant_guard B; change 4*B.basis.det.natAbs≤2^WordRAM.precision B; omega)
  let result := Called small (determinantPrepared d data)
  have global : GlobalControls B result := prepared.controls.transport (called_high small _)
  have retained (address : Nat) (before : address< inputEnd B+WordRAM.precision B) : result.2 address=data.2 address := by
    have equal := correct.frame address
      (Or.inl (by dsimp only [geometry,Circuit.slotBase]; unfold circuitBase; nlinarith))
      (Or.inl before) (Or.inl (by dsimp only [geometry]; omega))
    exact equal.trans (congrFun memory address)
  have naturalLength : Candidate.inputEnd B=inputEnd B := by
    simp only [Candidate.inputEnd,inputEnd,WordRAM.words_eq_map,List.length_map]
  refine ⟨result,8+cost,headers.seq (NaturalData.call_exec (s:=64) run),by exact Nat.add_le_add_left budget 8,?_,global.n,global.frontier⟩
  constructor
  · exact global.precision
  · rw [naturalLength]; exact global.zero
  · rw [naturalLength]; exact global.determinant
  · rw [naturalLength]; exact global.twice
  · rw [naturalLength]; exact global.parities
  · simpa only [Fin.val_mk,Nat.zero_mul,Nat.add_zero] using global.first
  · simpa only [Fin.val_mk,Nat.zero_mul,Nat.add_zero] using global.second
  · rw [naturalLength,global.frontier]
    have grow := Nat.mul_le_mul_right (WordRAM.precision B) (show 3+d≤factor d by unfold factor; omega)
    unfold endAddress; omega
  · intro address within
    rw [naturalLength] at within
    rw [retained address (by omega)]
    exact ready.original address within
  · intro i digit
    rw [naturalLength,retained _ (by omega)]
    exact ready.zero i digit
  · rw [naturalLength]; exact correct.absolute_bits
  · rw [naturalLength]; exact correct.twice_bits
  · rw [naturalLength]; exact correct.absolute_value
  · rw [naturalLength]; exact correct.twice_value
  · exact nonzero

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
