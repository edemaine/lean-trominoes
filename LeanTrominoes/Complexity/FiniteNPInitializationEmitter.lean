/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteNPCertificateStackEmitterCorrectness

/-! # Complete native verifier initialization program

Generate the fixed control/label prefix, empty noninput stacks, the source
prefix and bounded unknown certificate, and the three conjunction closers.
-/
noncomputable section
namespace LeanTrominoes.FiniteNPInitializationEmitter
open Computability Turing PeriodicCNF
open AffineEmitterPipeline UnaryProgramTokens UnaryProgramTokenAlgebra
open Complexity.VerifierInPolyTime FiniteNPCompilerPreparation
open FiniteNPMachineProgramEmitter (sourceSpace spaceCount_prepared)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack
abbrev Source := Symbol encoding.Γ

def stackPhases (stack : verifier.computer.tm.K) : List (Phase
    (SelectedPrefixMarkerMachine.Tagged 0 (Source (encoding := encoding)))) :=
  if stack=verifier.computer.tm.k₀ then
    [BoundedMachineOneHotEmitter.fixedPhase (ofProgram (TransitionProgram.constant true))]
  else BoundedMachineFixedConfigurationEmitter.stackPhases (tm := verifier.computer.tm)
    (isCounter 2) .current (initList verifier.computer.tm []) stack

def otherPhases : List (Phase (SelectedPrefixMarkerMachine.Tagged 0
    (Source (encoding := encoding)))) :=
  (BoundedMachineAtom.finiteValues verifier.computer.tm.K).flatMap (stackPhases verifier)++
    [BoundedMachineOneHotEmitter.fixedPhase (allEnding (Fintype.card verifier.computer.tm.K))]

def otherTokens (symbols : List encoding.Γ) : List Token :=
  emittedAll (otherPhases verifier)
    (SelectedPrefixMarkerMachine.mark (isCounter 2) 0 (prepared verifier symbols))

theorem stackPhases_eq (stack : verifier.computer.tm.K) (symbols : List encoding.Γ) :
    emittedAll (stackPhases verifier stack)
      (SelectedPrefixMarkerMachine.mark (isCounter 2) 0 (prepared verifier symbols))=
      ofProgram (if stack=verifier.computer.tm.k₀ then TransitionProgram.constant true
        else BoundedMachineProgram.currentStackIs (tm := verifier.computer.tm)
          (space := sourceSpace verifier symbols) (initList verifier.computer.tm []) stack) := by
  by_cases same : stack=verifier.computer.tm.k₀
  · simp [stackPhases,same,emittedAll,BoundedMachineOneHotEmitter.fixedPhase_emitted]
  · simp only [stackPhases,if_neg same]
    exact BoundedMachineFixedConfigurationEmitter.emittedAll_stackPhases (isCounter 2) .current
      (initList verifier.computer.tm []) stack (by simp [initList,same]) (prepared verifier symbols)
      _ (by simp [initList,same]) (spaceCount_prepared verifier symbols)

theorem otherTokens_eq (symbols : List encoding.Γ) : otherTokens verifier symbols=
    ofProgram (FiniteCertificate.otherStacks verifier.computer.tm (sourceSpace verifier symbols)).program := by
  unfold otherTokens otherPhases FiniteCertificate.otherStacks
  rw [BoundedMachineOneHotEmitter.emittedAll_append,BoundedMachineWellFormedEmitter.emittedAll_flatMap]
  simp only [TransitionExpr.program_all,List.map_map,Function.comp_def,ofProgram_all,
    List.length_map,BoundedMachineAtom.finiteValues_length]
  congr 1
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro stack _
    rw [stackPhases_eq]
    by_cases same : stack=verifier.computer.tm.k₀ <;> simp [same]
  · simp [emittedAll,BoundedMachineOneHotEmitter.fixedPhase_emitted]

def otherComputableInPolyTime : TM2ComputableInPolyTime id id (otherTokens verifier) := by
  unfold otherTokens
  let marked := TM2CompositionMachine.computableInPolyTime
    (FiniteNPCompilerPreparation.computableInPolyTime verifier)
    (SelectedPrefixMarkerMachine.computableInPolyTime (isCounter 2) 0)
  exact TM2CompositionMachine.computableInPolyTime marked
    (emittedAllComputableInPolyTime (otherPhases verifier))

def fixedPrefix : List Token :=
  ofProgram (BoundedMachineProgram.currentLabelIs (tm := verifier.computer.tm) (some verifier.computer.tm.main))++
    ofProgram (BoundedMachineProgram.currentControlIs (tm := verifier.computer.tm) verifier.computer.tm.initialState)

def fixedEnding : List Token := instructionTokens .conjoin++instructionTokens .conjoin++instructionTokens .conjoin

def initialProgram (symbols : List encoding.Γ) : TransitionProgram.Program :=
  (FiniteCertificate.initialExpression verifier.computer.tm (sourceSpace verifier symbols)
    (FiniteNPCertificateStackEmitter.initialWord verifier symbols) (certificateBit verifier)
    (verifier.witnessBound.eval symbols.length)).program

def tokens (symbols : List encoding.Γ) : List Token :=
  fixedPrefix verifier++otherTokens verifier symbols++
    ofProgram (FiniteNPCertificateStackEmitter.stackProgram verifier symbols)++fixedEnding

theorem tokens_eq (symbols : List encoding.Γ) : tokens verifier symbols=ofProgram (initialProgram verifier symbols) := by
  rw [tokens,otherTokens_eq,FiniteNPCertificateStackEmitter.stackProgram_eq]
  simp [initialProgram,FiniteCertificate.initialExpression,fixedPrefix,fixedEnding,
    TransitionExpr.program,TransitionProgram.conjoin,List.append_assoc,ofProgram]

def computableInPolyTime : TM2ComputableInPolyTime id id
    (fun symbols => ofProgram (initialProgram verifier symbols)) := by
  let prefixComputer : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => fixedPrefix verifier) := TM2ConstantValueCompiler.computableInPolyTime id id (fixedPrefix verifier)
  let first := TM2ListAppend.nativeComputableInPolyTime prefixComputer (otherComputableInPolyTime verifier)
  let body := TM2ListAppend.nativeComputableInPolyTime first
    (FiniteNPCertificateStackEmitter.computableInPolyTime verifier)
  let endingComputer : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => fixedEnding) := TM2ConstantValueCompiler.computableInPolyTime id id fixedEnding
  exact TM2ComputableInPolyTime.of_eq (TM2ListAppend.nativeComputableInPolyTime body endingComputer) (tokens_eq verifier)

theorem initialProgram_encode (input : Input) : initialProgram verifier (encoding.encode input)=
    (FiniteCertificate.initialExpression verifier.computer.tm (spaceLimit verifier input)
      (initialPrefix verifier input) (certificateBit verifier)
      (verifier.witnessBound.eval (encoding.encode input).length)).program := by
  simp [initialProgram,sourceSpace,spaceLimit,FiniteNPCertificateStackEmitter.initialWord_encode]

end LeanTrominoes.FiniteNPInitializationEmitter
