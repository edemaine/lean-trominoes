/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAbsoluteTokenCompiler
import LeanTrominoes.FiniteNPVariableNameCompiler
import LeanTrominoes.FiniteNPPaddedProgramEmitter
import LeanTrominoes.PeriodicCNFUnaryProgramTokenFinalizer

/-! # Native polynomial headers and postorder-program assembly -/
noncomputable section
namespace LeanTrominoes.FiniteNPTokenAssembly
open Computability Turing PeriodicCNF UnaryProgramTokens UnaryProgramTokenAlgebra
open UnaryFieldEncoderMachine (unaryFields unaryField)
open FiniteNPCompilerPreparation
variable {Source : Type} [Fintype Source]

private def onFields {Target : Type} [Fintype Target] [Inhabited Target]
    (block : UnaryFieldEncoderMachine.Symbol → List Target) :
    TM2ComputableInPolyTime unaryFields id (fun fields => (unaryFields fields).flatMap block) :=
  TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime block) (fun _ => rfl) (fun _ => rfl)

/-- Evaluate any fixed natural polynomial on the length of the source word. -/
def polynomialScalar (polynomial : Polynomial Nat) :
    TM2ComputableInPolyTime (id : List Source → List Source) unaryFields
      (fun word => [polynomial.eval word.length]) := by
  let embedded := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : Source => [(Sum.inl symbol : Symbol Source)])
  let padded := TM2CompositionMachine.computableInPolyTime embedded
    (addCounterComputableInPolyTime 0 polynomial)
  let counted := TM2CompositionMachine.computableInPolyTime padded
    (counterComputableInPolyTime (Source := Source) 0)
  apply TM2ComputableInPolyTime.of_eq counted
  intro word
  simp only [← List.map_eq_flatMap]
  simp [addCounter]

def freshBlock : UnaryFieldEncoderMachine.Symbol → List Token
  | .unit => [.freshUnit]
  | .delimiter => [.freshEnd]

theorem freshBlock_fields (fresh : Nat) :
    (unaryFields [fresh]).flatMap freshBlock=freshTokens fresh := by
  have units : (List.replicate fresh UnaryFieldEncoderMachine.Symbol.unit).flatMap freshBlock=
      List.replicate fresh Token.freshUnit := by
    induction fresh <;> simp_all [List.replicate_succ,freshBlock]
  simp [unaryFields,unaryField,freshTokens,freshBlock,units]

def freshCompiler {fresh : List Source → Nat}
    (scalar : UnaryColumn.ScalarCompiler fresh) :
    TM2ComputableInPolyTime id id (fun word => freshTokens (fresh word)) := by
  let printed := TM2CompositionMachine.computableInPolyTime scalar
    (onFields freshBlock)
  exact TM2ComputableInPolyTime.of_eq printed (fun _ => freshBlock_fields _)

def endingBlock : UnaryFieldEncoderMachine.Symbol → List Token
  | .unit => instructionTokens .conjoin
  | .delimiter => []

theorem allEnding_eq (count : Nat) : allEnding count=
    instructionTokens (.constant true)++(List.replicate count (instructionTokens .conjoin)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [allEnding,foldEnding] at *
    rw [ih,List.replicate_succ',List.flatten_append]
    simp [List.append_assoc]

def endingCompiler {count : List Source → Nat}
    (scalar : UnaryColumn.ScalarCompiler count) :
    TM2ComputableInPolyTime id id (fun word => allEnding (count word)) := by
  let body := TM2CompositionMachine.computableInPolyTime scalar
    (onFields endingBlock)
  let first : TM2ComputableInPolyTime (id : List Source → List Source) id
      (fun _ => instructionTokens (.constant true)) :=
    TM2ConstantValueCompiler.computableInPolyTime id id (instructionTokens (.constant true))
  apply TM2ComputableInPolyTime.of_eq (TM2ListAppend.nativeComputableInPolyTime first body)
  intro word
  have units (n : Nat) :
      (List.replicate n UnaryFieldEncoderMachine.Symbol.unit).flatMap endingBlock=
        (List.replicate n (instructionTokens .conjoin)).flatten := by
    induction n <;> simp_all [List.replicate_succ,endingBlock]
  simp [unaryFields,unaryField,endingBlock,allEnding_eq,units]

def currentToken : Token → Token
  | .wireStart _ => .wireStart false
  | token => token

theorem currentToken_instruction (instruction : TransitionInstruction) :
    (instructionTokens instruction).map currentToken=
      instructionTokens (FiniteNPPaddedProgramEmitter.retime .current instruction) := by
  cases instruction with
  | wire wire =>
    cases wire with
    | mk slice atom =>
      cases slice <;> simp [instructionTokens,currentToken,FiniteNPPaddedProgramEmitter.retime,
        clauseTokens,atomTokens,ProgramTokens.sliceBool]
  | _ => simp [instructionTokens,currentToken,FiniteNPPaddedProgramEmitter.retime,clauseTokens]

def currentCompiler {program : List Source → TransitionProgram.Program}
    (emitter : TM2ComputableInPolyTime id id (fun word => ofProgram (program word))) :
    TM2ComputableInPolyTime id id (fun word => ofProgram
      ((program word).map (FiniteNPPaddedProgramEmitter.retime .current))) := by
  let mapped := TM2CompositionMachine.computableInPolyTime emitter
    (FiniteBlockTransducer.computableInPolyTime (fun token => [currentToken token]))
  apply TM2ComputableInPolyTime.of_eq mapped
  intro word
  simp only [← List.map_eq_flatMap,ofProgram,List.map_flatMap,List.flatMap_map]
  exact List.flatMap_congr (fun instruction _ => currentToken_instruction instruction)

end LeanTrominoes.FiniteNPTokenAssembly
