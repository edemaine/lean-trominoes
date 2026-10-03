/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAbsoluteProgramCompiler
import LeanTrominoes.PeriodicCNFUnaryProgramTokens

/-! # Native columns extracted from verified unary program emitters

Two fixed block transducers extract finite instruction metadata and source
atom numbers from the existing emitter format. Cartesian column composition
then serializes the same program at every computed absolute time.
-/
noncomputable section
namespace LeanTrominoes.FiniteCNF.ProgramColumns
open Computability Turing PeriodicCNF UnaryColumn
open UnaryProgramTokens AbsoluteProgramCompiler
open UnaryFieldEncoderMachine (unaryField unaryFields)

def codeBlock : Token → List UnaryFieldEncoderMachine.Symbol
  | .constant false => unaryFields [0]
  | .constant true => unaryFields [1]
  | .wireStart false => unaryFields [2]
  | .wireStart true => unaryFields [3]
  | .negate => unaryFields [4]
  | .conjoin => unaryFields [5]
  | .disjoin => unaryFields [6]
  | _ => []

def atomBlock : Token → List UnaryFieldEncoderMachine.Symbol
  | .constant _ | .negate | .conjoin | .disjoin => unaryFields [0]
  | .atomUnit => [.unit]
  | .atomEnd => [.delimiter]
  | _ => []

private theorem atomBlock_units (n : Nat) :
    (List.replicate n Token.atomUnit).flatMap atomBlock=
      List.replicate n UnaryFieldEncoderMachine.Symbol.unit := by
  induction n <;> simp_all [List.replicate_succ,atomBlock]

private theorem codeBlock_units (n : Nat) :
    (List.replicate n Token.atomUnit).flatMap codeBlock=[] := by
  induction n <;> simp_all [List.replicate_succ,codeBlock]

private theorem codeBlock_instruction (instruction : TransitionInstruction) :
    (instructionTokens instruction).flatMap codeBlock=
      unaryFields [instructionCode instruction] := by
  cases instruction with
  | constant b => cases b <;> rfl
  | wire wire =>
    rcases wire with ⟨slice,atom⟩
    cases slice <;> simp [instructionTokens,clauseTokens,atomTokens,codeBlock,
      codeBlock_units,instructionCode,ProgramTokens.sliceBool]
  | negate | conjoin | disjoin => rfl

private theorem atomBlock_instruction (instruction : TransitionInstruction) :
    (instructionTokens instruction).flatMap atomBlock=
      unaryFields [instructionAtom instruction] := by
  cases instruction with
  | constant b => cases b <;> rfl
  | wire wire =>
    rcases wire with ⟨slice,atom⟩
    cases slice <;> simp [instructionTokens,clauseTokens,atomTokens,atomBlock,
      atomBlock_units,instructionAtom,ProgramTokens.sliceBool,unaryFields,unaryField]
  | negate | conjoin | disjoin => rfl

theorem codeBlock_ofProgram (program : List TransitionInstruction) :
    (ofProgram program).flatMap codeBlock=unaryFields (program.map instructionCode) := by
  induction program with
  | nil => rfl
  | cons instruction program ih =>
    simp only [ofProgram,List.flatMap_cons,List.flatMap_append,codeBlock_instruction,
      List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons,
      UnaryFieldEncoderMachine.unaryFields_nil,List.append_nil] at ih ⊢
    exact congrArg (unaryField (instructionCode instruction) ++ ·) ih

theorem atomBlock_ofProgram (program : List TransitionInstruction) :
    (ofProgram program).flatMap atomBlock=unaryFields (program.map instructionAtom) := by
  induction program with
  | nil => rfl
  | cons instruction program ih =>
    simp only [ofProgram,List.flatMap_cons,List.flatMap_append,atomBlock_instruction,
      List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons,
      UnaryFieldEncoderMachine.unaryFields_nil,List.append_nil] at ih ⊢
    exact congrArg (unaryField (instructionAtom instruction) ++ ·) ih

variable {Source : Type} [Fintype Source] [Inhabited Source]
  {program : List Source → List TransitionInstruction}

def codes (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s))) :
    Compiler program (fun _ instruction => instructionCode instruction) := by
  let physical := TM2CompositionMachine.computableInPolyTime emitter
    (FiniteBlockTransducer.computableInPolyTime codeBlock)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (fun s => codeBlock_ofProgram (program s))

def atoms (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s))) :
    Compiler program (fun _ instruction => instructionAtom instruction) := by
  let physical := TM2CompositionMachine.computableInPolyTime emitter
    (FiniteBlockTransducer.computableInPolyTime atomBlock)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (fun s => atomBlock_ofProgram (program s))

/-- One emitted program is renamed and serialized at every supplied time,
using finite machines for all metadata, Cartesian, and arithmetic passes. -/
def repeated {count : List Source → Nat}
    (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s)))
    (bound : ScalarCompiler count) :
    TM2ComputableInPolyTime id unaryFields (fun s =>
      (List.range (count s)).flatMap fun time => transitionProgramFields
        ((program s).map (absoluteInstruction time))) := by
  let range := naturalRange bound
  let programCodes := codes emitter
  let programAtoms := atoms emitter
  let operationCodes := cartesianRight range programCodes
  let sourceAtoms := cartesianRight range programAtoms
  let times := cartesianLeft range programCodes
  let physical := AbsoluteProgramCompiler.computableInPolyTime operationCodes sourceAtoms times
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  congr 1
  simp [List.flatMap_assoc,List.flatMap_map,transitionProgramFields]

end LeanTrominoes.FiniteCNF.ProgramColumns
