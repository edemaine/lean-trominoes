/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPMachineProgramEmitter
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.PeriodicCNFMachineAllEndingEmitter

/-! # Native emission of bounded unknown-certificate stack tests

One cell descriptor per stack position records a source symbol, the witness
separator, a freely chosen certificate bit or empty cell, or a forced empty
tail. A fixed indexed affine machine emits the complete postorder stack test.
-/
noncomputable section
namespace LeanTrominoes.FiniteNPCertificateStackEmitter
open Computability Turing PeriodicCNF
open AffineEmitterPipeline UnaryProgramTokens UnaryProgramTokenAlgebra
open Complexity.VerifierInPolyTime FiniteNPCompilerPreparation
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack
abbrev Source := Symbol encoding.Γ

def tailPolynomial : Polynomial Nat :=
  timePolynomial verifier*Polynomial.C (TM2OutputLength.machinePushBound verifier.computer.tm)+
    Polynomial.C (acceptingWord verifier).length

def layout (symbols : List encoding.Γ) : List (Source (encoding := encoding)) :=
  addCounter 2 (tailPolynomial verifier)
    (addCounter 1 verifier.witnessBound
      (addCounter 0 1 (symbols.map Sum.inl)))

theorem layout_eq (symbols : List encoding.Γ) : layout verifier symbols=
    symbols.map Sum.inl++[.inr 0]++
      List.replicate (verifier.witnessBound.eval symbols.length) (.inr 1)++
      List.replicate ((tailPolynomial verifier).eval symbols.length) (.inr 2) := by
  simp [layout,addCounter,PeriodicCNF.PolySpaceRequestPadding.selectedCount_append,
    isSource,UnaryPolynomialPaddingMachine.selectedCount]

theorem layout_length (symbols : List encoding.Γ) :
    (layout verifier symbols).length=FiniteNPMachineProgramEmitter.sourceSpace verifier symbols := by
  rw [layout_eq]
  simp [FiniteNPMachineProgramEmitter.sourceSpace,spacePolynomial,tailPolynomial,Nat.add_assoc]
  omega

def layoutComputableInPolyTime : TM2ComputableInPolyTime id id (layout verifier) := by
  let embedded := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : encoding.Γ => [(Sum.inl symbol : Source (encoding := encoding))])
  let separated := TM2CompositionMachine.computableInPolyTime embedded (addCounterComputableInPolyTime 0 1)
  let certificate := TM2CompositionMachine.computableInPolyTime separated
    (addCounterComputableInPolyTime 1 verifier.witnessBound)
  let complete := TM2CompositionMachine.computableInPolyTime certificate
    (addCounterComputableInPolyTime 2 (tailPolynomial verifier))
  apply TM2ComputableInPolyTime.of_eq complete
  intro symbols
  simp [layout,← List.map_eq_flatMap]

def slotTemplate : Source (encoding := encoding) → AffineProgramTemplates.Program
  | .inl symbol => BoundedMachineAffineProgram.currentStackCellIs
      (tm := verifier.computer.tm) verifier.computer.tm.k₀ 0
      (some (verifier.computer.inputAlphabet.invFun (.inl symbol)))
  | .inr tag =>
    if tag=0 then BoundedMachineAffineProgram.currentStackCellIs
      (tm := verifier.computer.tm) verifier.computer.tm.k₀ 0
      (some (verifier.computer.inputAlphabet.invFun (.inr none)))
    else if tag=1 then AffineProgramTemplates.disjoin
      (BoundedMachineAffineProgram.currentStackCellIs (tm := verifier.computer.tm)
        verifier.computer.tm.k₀ 0 none)
      (AffineProgramTemplates.disjoin
        (BoundedMachineAffineProgram.currentStackCellIs (tm := verifier.computer.tm)
          verifier.computer.tm.k₀ 0 (some (certificateBit verifier false)))
        (BoundedMachineAffineProgram.currentStackCellIs (tm := verifier.computer.tm)
          verifier.computer.tm.k₀ 0 (some (certificateBit verifier true))))
    else BoundedMachineAffineProgram.currentStackCellIs
      (tm := verifier.computer.tm) verifier.computer.tm.k₀ 0 none

def family : IndexedTemplateEmitter.Family (Source (encoding := encoding)) :=
  fun descriptor => some (slotTemplate verifier descriptor).recipes

def slotPrograms : Nat → List (Source (encoding := encoding)) → List TransitionProgram.Program
  | _, [] => []
  | position, descriptor :: descriptors =>
    (slotTemplate verifier descriptor).evaluate position :: slotPrograms (position+1) descriptors

@[simp] theorem slotPrograms_length (position : Nat) (word : List (Source (encoding := encoding))) :
    (slotPrograms verifier position word).length=word.length := by
  induction word generalizing position <;> simp_all [slotPrograms]

theorem emittedAux_eq (position : Nat) (word : List (Source (encoding := encoding))) :
    IndexedTemplateEmitter.emittedAux (family verifier) position word=
      (slotPrograms verifier position word).flatMap ofProgram := by
  induction word generalizing position with
  | nil => rfl
  | cons descriptor word ih =>
    simp [IndexedTemplateEmitter.emittedAux,family,slotPrograms,
      AffineProgramTemplates.Program.positionTokens_recipes,ih]

def operands (symbols : List encoding.Γ) : List Token :=
  IndexedTemplateEmitter.emitted (family verifier) (layout verifier symbols)

def operandsComputableInPolyTime : TM2ComputableInPolyTime id id (operands verifier) := by
  let printed := TM2CompositionMachine.computableInPolyTime (layoutComputableInPolyTime verifier)
    (IndexedTemplateEmitterMachine.computableInPolyTime (family verifier))
  let complete := TM2CompositionMachine.computableInPolyTime printed
    (extractTokensComputableInPolyTime (Data := Source (encoding := encoding)))
  apply TM2ComputableInPolyTime.of_eq complete
  intro symbols
  simp [IndexedTemplateEmitterMachine.appendedOutput,extractTokens,List.flatMap_map,operands]

def ending (symbols : List encoding.Γ) : List Token :=
  extractTokens (BoundedMachineAllEndingEmitter.run (fun _ : Source (encoding := encoding) => true)
    (embedData (layout verifier symbols)))

theorem ending_eq (symbols : List encoding.Γ) :
    ending verifier symbols=allEnding (layout verifier symbols).length := by
  unfold ending
  rw [BoundedMachineAllEndingEmitter.run_eq_append,selectedCount_embedData]
  have count (word : List (Source (encoding := encoding))) :
      UnaryPolynomialPaddingMachine.selectedCount (fun _ => true) word=word.length := by
    induction word <;> simp_all [UnaryPolynomialPaddingMachine.selectedCount,Nat.add_comm]
  rw [count]
  simp [extractTokens,embedData,List.flatMap_map]

def endingComputableInPolyTime : TM2ComputableInPolyTime id id (ending verifier) := by
  unfold ending
  let embedded := TM2CompositionMachine.computableInPolyTime (layoutComputableInPolyTime verifier)
    (embedDataComputableInPolyTime (Data := Source (encoding := encoding)))
  let printed := TM2CompositionMachine.computableInPolyTime embedded
    (BoundedMachineAllEndingEmitter.computableInPolyTime (fun _ : Source (encoding := encoding) => true))
  exact TM2CompositionMachine.computableInPolyTime printed
    (extractTokensComputableInPolyTime (Data := Source (encoding := encoding)))

def stackProgram (symbols : List encoding.Γ) : TransitionProgram.Program :=
  TransitionProgram.all (slotPrograms verifier 0 (layout verifier symbols))

def tokens (symbols : List encoding.Γ) : List Token := operands verifier symbols++ending verifier symbols

theorem tokens_eq (symbols : List encoding.Γ) : tokens verifier symbols=ofProgram (stackProgram verifier symbols) := by
  simp [tokens,operands,IndexedTemplateEmitter.emitted,emittedAux_eq,ending_eq,stackProgram]

def computableInPolyTime : TM2ComputableInPolyTime id id (fun symbols => ofProgram (stackProgram verifier symbols)) :=
  TM2ComputableInPolyTime.of_eq
    (TM2ListAppend.nativeComputableInPolyTime (operandsComputableInPolyTime verifier)
      (endingComputableInPolyTime verifier)) (tokens_eq verifier)

end LeanTrominoes.FiniteNPCertificateStackEmitter
