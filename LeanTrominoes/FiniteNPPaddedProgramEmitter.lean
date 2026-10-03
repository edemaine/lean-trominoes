/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPMachineProgramEmitter
import LeanTrominoes.FinitePaddedMachineStep

/-! # Native accepting-self-loop program generation -/
noncomputable section
namespace LeanTrominoes.FiniteNPPaddedProgramEmitter
open Computability Turing PeriodicCNF
open UnaryProgramTokens UnaryProgramTokenAlgebra
open Complexity.VerifierInPolyTime FiniteNPMachineProgramEmitter
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def program (symbols : List encoding.Γ) : TransitionProgram.Program :=
  TransitionProgram.disjoin
    (BoundedMachineProgram.machineStep (tm := verifier.computer.tm) (space := sourceSpace verifier symbols))
    (TransitionProgram.conjoin
      (BoundedMachineFixedConfigurationEmitter.configurationIs (tm := verifier.computer.tm) .current
        (acceptingConfiguration verifier) (sourceSpace verifier symbols))
      (BoundedMachineFixedConfigurationEmitter.configurationIs (tm := verifier.computer.tm) .next
        (acceptingConfiguration verifier) (sourceSpace verifier symbols)))

def ending : List Token := instructionTokens .conjoin++instructionTokens .disjoin

def tokens (symbols : List encoding.Γ) : List Token :=
  stepTokens verifier symbols++acceptingTokens verifier .current symbols++
    acceptingTokens verifier .next symbols++ending

theorem tokens_eq (symbols : List encoding.Γ) : tokens verifier symbols=ofProgram (program verifier symbols) := by
  simp [tokens,program,ending,stepTokens_eq,acceptingTokens_eq,ofProgram_conjoin,ofProgram_disjoin,List.append_assoc]

def computableInPolyTime : TM2ComputableInPolyTime id id (fun symbols => ofProgram (program verifier symbols)) := by
  let first := TM2ListAppend.nativeComputableInPolyTime (stepComputableInPolyTime verifier)
    (acceptingComputableInPolyTime verifier .current)
  let body := TM2ListAppend.nativeComputableInPolyTime first (acceptingComputableInPolyTime verifier .next)
  let closing : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => ending) := TM2ConstantValueCompiler.computableInPolyTime id id ending
  exact TM2ComputableInPolyTime.of_eq (TM2ListAppend.nativeComputableInPolyTime body closing) (tokens_eq verifier)

def retime (slice : TransitionSlice) : TransitionInstruction → TransitionInstruction
  | .wire wire => .wire ⟨slice,wire.atom⟩
  | instruction => instruction

theorem atCurrent_program (expression : TransitionExpr) : expression.atCurrent.program=
    expression.program.map (retime .current) := by
  induction expression <;> simp_all [TransitionExpr.atCurrent,TransitionExpr.program,
    TransitionProgram.constant,TransitionProgram.wire,TransitionProgram.negate,
    TransitionProgram.conjoin,TransitionProgram.disjoin,retime]

theorem atNext_program (expression : TransitionExpr) : expression.atNext.program=
    expression.program.map (retime .next) := by
  induction expression <;> simp_all [TransitionExpr.atNext,TransitionExpr.program,
    TransitionProgram.constant,TransitionProgram.wire,TransitionProgram.negate,
    TransitionProgram.conjoin,TransitionProgram.disjoin,retime]

private theorem map_all (slice : TransitionSlice) (programs : List TransitionProgram.Program) :
    (TransitionProgram.all programs).map (retime slice)=
      TransitionProgram.all (programs.map (List.map (retime slice))) := by
  induction programs <;> simp_all [TransitionProgram.all,TransitionProgram.constant,
    TransitionProgram.conjoin,retime]

private theorem map_configuration (slice : TransitionSlice) (space : Nat) (target : verifier.computer.tm.Cfg) :
    (BoundedMachineProgram.currentConfigIs (tm := verifier.computer.tm) (space := space) target).map (retime slice)=
      BoundedMachineFixedConfigurationEmitter.configurationIs (tm := verifier.computer.tm) slice target space := by
  cases slice <;> simp [BoundedMachineFixedConfigurationEmitter.configurationIs,
    BoundedMachineFixedConfigurationEmitter.labelIs,BoundedMachineFixedConfigurationEmitter.controlIs,
    BoundedMachineFixedConfigurationEmitter.stackIs,BoundedMachineFixedConfigurationEmitter.stackCellIs,
    BoundedMachineProgram.currentConfigIs,BoundedMachineProgram.currentStackIs,
    BoundedMachineProgram.currentLabelIs,BoundedMachineProgram.nextLabelIs,
    BoundedMachineProgram.currentControlIs,BoundedMachineProgram.nextControlIs,
    BoundedMachineProgram.currentStackCellIs,BoundedMachineProgram.nextStackCellIs,
    TransitionProgram.conjoin,TransitionProgram.current,TransitionProgram.next,TransitionProgram.wire,
    map_all,List.map_map,Function.comp_def,retime]

theorem program_eq (symbols : List encoding.Γ) : program verifier symbols=
    (FiniteMachineTrace.paddedStep verifier.computer.tm (sourceSpace verifier symbols)
      (acceptingConfiguration verifier)).program := by
  simp only [program,FiniteMachineTrace.paddedStep,TransitionExpr.program_or,
    TransitionExpr.program_and,BoundedMachineProgram.program_machineStepExpression,
    atCurrent_program,atNext_program,BoundedMachineProgram.program_currentConfigIs,
    map_configuration]

end LeanTrominoes.FiniteNPPaddedProgramEmitter
