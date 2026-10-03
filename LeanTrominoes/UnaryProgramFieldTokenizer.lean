/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramColumns
import LeanTrominoes.FiniteStateTransducerTime

/-! # Recovering weighted program tokens from native unary fields

This finite-state pass supplies the exact clause markers consumed by the
existing request finalizer after absolute-time program serialization.
-/
noncomputable section
namespace LeanTrominoes.UnaryProgramFieldTokenizer
open Computability Turing PeriodicCNF FiniteStateTransducer UnaryProgramTokens
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)

inductive State
  | tag (count : Fin 6)
  | constant (value : Bool)
  | slice (next : Bool)
  | atom
  deriving Fintype

def increment (count : Fin 6) : Fin 6 := ⟨min (count.val+1) 5,by omega⟩

def transition : State → Symbol → State × List Token
  | .tag count, .unit => (.tag (increment count),[])
  | .tag count, .delimiter =>
    match count.val with
    | 0 => (.constant false,[])
    | 1 => (.slice false,clauseTokens 2)
    | 2 => (.tag 0,instructionTokens .negate)
    | 3 => (.tag 0,instructionTokens .conjoin)
    | 4 => (.tag 0,instructionTokens .disjoin)
    | _ => (.tag 0,[])
  | .constant _, .unit => (.constant true,[])
  | .constant value, .delimiter => (.tag 0,instructionTokens (.constant value))
  | .slice _, .unit => (.slice true,[])
  | .slice next, .delimiter => (.atom,[.wireStart next])
  | .atom, .unit => (.atom,[.atomUnit])
  | .atom, .delimiter => (.tag 0,[.atomEnd])

def tokens : List Symbol → List Token := output (.tag 0) transition (fun _ => [])

private theorem scan_atom_units (n : Nat) :
    scan transition .atom (List.replicate n Symbol.unit)=
      (.atom,List.replicate n Token.atomUnit) := by
  induction n <;> simp_all [List.replicate_succ,scan,transition]

private theorem scan_instruction (instruction : TransitionInstruction) :
    scan transition (.tag 0) (unaryFields instruction.fields)=
      (.tag 0,instructionTokens instruction) := by
  cases instruction with
  | constant value => cases value <;> rfl
  | wire wire =>
    rcases wire with ⟨slice,atom⟩
    cases slice <;> simp [TransitionInstruction.fields,unaryFields,unaryField,
      scan_append,scan,transition,increment,scan_atom_units,instructionTokens,
      ProgramTokens.sliceBool,clauseTokens,atomTokens,List.append_assoc]
  | negate | conjoin | disjoin => rfl

private theorem scan_program (program : TransitionProgram.Program) :
    scan transition (.tag 0) (unaryFields (transitionProgramFields program))=
      (.tag 0,ofProgram program) := by
  induction program with
  | nil => rfl
  | cons instruction program ih =>
    simp only [transitionProgramFields,List.flatMap_cons,UnaryFieldEncoderMachine.unaryFields_append,
      scan_append,scan_instruction,ofProgram,List.flatMap_cons] at ih ⊢
    rw [ih]

theorem tokens_fields (program : TransitionProgram.Program) :
    tokens (unaryFields (transitionProgramFields program))=ofProgram program := by
  simp [tokens,output,scan_program]

def computableInPolyTime : TM2ComputableInPolyTime id id tokens := by
  unfold tokens
  exact FiniteStateTransducer.computableInPolyTime (.tag 0) transition (fun _ => [])

/-- Reattach exact Tseitin clause weights to a serialized postorder program. -/
def ofFields {Input Source : Type} [Fintype Source]
    {encode : Input → List Source} {program : Input → TransitionProgram.Program}
    (fields : TM2ComputableInPolyTime encode unaryFields
      (fun input => transitionProgramFields (program input))) :
    TM2ComputableInPolyTime encode id (fun input => ofProgram (program input)) := by
  let tokenizer := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields computableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  let physical := TM2CompositionMachine.computableInPolyTime fields tokenizer
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (fun input => tokens_fields (program input))

end LeanTrominoes.UnaryProgramFieldTokenizer
