/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPCertificateStackEmitter
import LeanTrominoes.FiniteCertificateInitialization
import Mathlib.Data.List.GetD

/-! # Exact certificate-stack emission for the existing finite tableau -/
noncomputable section
namespace LeanTrominoes.FiniteNPCertificateStackEmitter
open Computability Turing PeriodicCNF
open Complexity.VerifierInPolyTime FiniteNPCompilerPreparation
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def initialDescriptors (symbols : List encoding.Γ) : List (Source (encoding := encoding)) :=
  symbols.map Sum.inl++[.inr 0]

def initialWord (symbols : List encoding.Γ) : List (verifier.computer.tm.Γ verifier.computer.tm.k₀) :=
  symbols.map (fun symbol => verifier.computer.inputAlphabet.invFun (.inl symbol))++
    [verifier.computer.inputAlphabet.invFun (.inr none)]

@[simp] theorem initialWord_length (symbols : List encoding.Γ) :
    (initialWord verifier symbols).length=symbols.length+1 := by simp [initialWord]

def fixedSymbol : Source (encoding := encoding) → Option (verifier.computer.tm.Γ verifier.computer.tm.k₀)
  | .inl symbol => some (verifier.computer.inputAlphabet.invFun (.inl symbol))
  | .inr tag => if tag=0 then some (verifier.computer.inputAlphabet.invFun (.inr none)) else none

theorem map_fixedSymbol (symbols : List encoding.Γ) :
    (initialDescriptors (encoding := encoding) symbols).map (fixedSymbol verifier)=
      (initialWord verifier symbols).map some := by
  simp [initialDescriptors,initialWord,fixedSymbol,List.map_map]

private theorem fixedSlot (symbols : List encoding.Γ) (descriptor : Source (encoding := encoding))
    (member : descriptor ∈ initialDescriptors (encoding := encoding) symbols) (position : Nat) :
    (slotTemplate verifier descriptor).evaluate position=
      BoundedMachineProgram.currentStackCellIs (tm := verifier.computer.tm) verifier.computer.tm.k₀
        position (fixedSymbol verifier descriptor) := by
  simp only [initialDescriptors,List.mem_append,List.mem_map,List.mem_singleton] at member
  rcases member with ⟨symbol,_,rfl⟩ | rfl <;>
    simp [slotTemplate,fixedSymbol]

private theorem slotPrograms_getD (word : List (Source (encoding := encoding))) (offset index : Nat)
    (small : index < word.length) :
    (slotPrograms verifier offset word).getD index []=
      (slotTemplate verifier (word.getD index (.inr 2))).evaluate (offset+index) := by
  induction word generalizing offset index with
  | nil => simp at small
  | cons descriptor word ih =>
    cases index with
    | zero => simp [slotPrograms]
    | succ index =>
      have small' : index < word.length := by simpa using small
      simpa [slotPrograms,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (offset+1) index small'

theorem layout_split (symbols : List encoding.Γ) : layout verifier symbols=
    initialDescriptors (encoding := encoding) symbols++
      (List.replicate (verifier.witnessBound.eval symbols.length) (.inr 1)++
        List.replicate ((tailPolynomial verifier).eval symbols.length) (.inr 2)) := by
  simp [layout_eq,initialDescriptors,List.append_assoc]

theorem slotTemplate_getD (symbols : List encoding.Γ)
    (index : Fin (FiniteNPMachineProgramEmitter.sourceSpace verifier symbols)) :
    (slotTemplate verifier ((layout verifier symbols).getD index.val (.inr 2))).evaluate index.val=
      (FiniteCertificate.cellExpression verifier.computer.tm
        (FiniteNPMachineProgramEmitter.sourceSpace verifier symbols) verifier.computer.tm.k₀
        (initialWord verifier symbols) (certificateBit verifier)
        (verifier.witnessBound.eval symbols.length) index).program := by
  unfold FiniteCertificate.cellExpression
  by_cases initial : index.val < (initialWord verifier symbols).length
  · rw [if_pos initial,layout_split]
    have descriptorSmall : index.val < (initialDescriptors (encoding := encoding) symbols).length := by
      simpa [initialDescriptors] using initial
    rw [List.getD_append _ _ _ _ descriptorSmall]
    rw [fixedSlot verifier symbols _ (by
      rw [List.getD_eq_getElem _ _ descriptorSmall]
      exact List.getElem_mem _) index.val,BoundedMachineProgram.program_currentStackCellIs]
    congr 1
    have mapEq := congrArg (fun word => word.getD index.val none) (map_fixedSymbol verifier symbols)
    simpa [List.getD_eq_getElem _ _ descriptorSmall,List.getD_eq_getElem _ _ initial,
      List.getElem?_eq_getElem initial,List.getElem?_eq_getElem descriptorSmall] using mapEq
  · rw [if_neg initial,layout_split]
    have descriptorLate : (initialDescriptors (encoding := encoding) symbols).length ≤ index.val := by
      simpa [initialDescriptors] using (Nat.le_of_not_gt initial)
    rw [List.getD_append_right _ _ _ _ descriptorLate]
    by_cases certificate : index.val < (initialWord verifier symbols).length+
        verifier.witnessBound.eval symbols.length
    · rw [if_pos certificate]
      have small : index.val-(initialDescriptors (encoding := encoding) symbols).length <
          verifier.witnessBound.eval symbols.length := by
        simp [initialDescriptors] at *; omega
      rw [List.getD_append _ _ _ _ (by simpa using small),List.getD_replicate _ small]
      simp [slotTemplate,TransitionProgram.disjoin]
    · rw [if_neg certificate]
      have late : (List.replicate (verifier.witnessBound.eval symbols.length)
          (Sum.inr 1 : Source (encoding := encoding))).length ≤
          index.val-(initialDescriptors (encoding := encoding) symbols).length := by
        simp [initialDescriptors] at *; omega
      rw [List.getD_append_right _ _ _ _ late]
      have lengthEq := layout_length verifier symbols
      rw [layout_eq] at lengthEq
      simp only [List.length_append,List.length_map,List.length_singleton,List.length_replicate] at lengthEq
      have small : index.val-(initialDescriptors (encoding := encoding) symbols).length-
          verifier.witnessBound.eval symbols.length < (tailPolynomial verifier).eval symbols.length := by
        have := index.isLt
        simp [initialDescriptors] at *; omega
      simp only [List.length_replicate]
      rw [List.getD_replicate _ small]
      simp [slotTemplate]

theorem stackProgram_eq (symbols : List encoding.Γ) : stackProgram verifier symbols=
    (FiniteCertificate.stackExpression verifier.computer.tm
      (FiniteNPMachineProgramEmitter.sourceSpace verifier symbols) verifier.computer.tm.k₀
      (initialWord verifier symbols) (certificateBit verifier)
      (verifier.witnessBound.eval symbols.length)).program := by
  unfold stackProgram FiniteCertificate.stackExpression
  rw [TransitionExpr.program_all]
  congr 1
  apply List.ext_getElem
  · simp [layout_length]
  · intro i left right
    have small : i < (layout verifier symbols).length := by simpa using left
    have spaceSmall : i < FiniteNPMachineProgramEmitter.sourceSpace verifier symbols := by
      simpa [layout_length] using small
    rw [← List.getD_eq_getElem _ [] left,slotPrograms_getD verifier _ 0 i small]
    simpa using slotTemplate_getD verifier symbols ⟨i,spaceSmall⟩

def tableauStackComputableInPolyTime : TM2ComputableInPolyTime id id (fun symbols =>
    UnaryProgramTokens.ofProgram (FiniteCertificate.stackExpression verifier.computer.tm
      (FiniteNPMachineProgramEmitter.sourceSpace verifier symbols) verifier.computer.tm.k₀
      (initialWord verifier symbols) (certificateBit verifier)
      (verifier.witnessBound.eval symbols.length)).program) :=
  TM2ComputableInPolyTime.of_eq (computableInPolyTime verifier)
    (fun symbols => congrArg UnaryProgramTokens.ofProgram (stackProgram_eq verifier symbols))

theorem initialWord_encode (input : Input) : initialWord verifier (encoding.encode input)=initialPrefix verifier input := by
  simp [initialWord,initialPrefix,List.map_append,List.map_map]

end LeanTrominoes.FiniteNPCertificateStackEmitter
