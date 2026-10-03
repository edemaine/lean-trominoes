/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPTokenAssembly
import LeanTrominoes.FiniteNPSeparatedRequest

/-! # Complete polynomial-time finite NP tableau request emission -/
noncomputable section
namespace LeanTrominoes.FiniteNPRequestEmitter
open Computability Turing PeriodicCNF UnaryProgramTokens UnaryProgramTokenAlgebra
open UnaryFieldEncoderMachine (unaryFields)
open Complexity.VerifierInPolyTime FiniteNPMachineProgramEmitter FiniteNPTokenAssembly
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

private def tableauCompiler {Source : Type} [Fintype Source]
    {expression : List Source → TransitionExpr} {count : List Source → Nat}
    (emitter : TM2ComputableInPolyTime id id (fun word => ofProgram (expression word).program))
    (scalar : UnaryColumn.ScalarCompiler count) :
    TM2ComputableInPolyTime id id (fun word => ofProgram
      (FiniteCNF.tableauExpression (fun _ => expression word) (count word)).program) := by
  let body := FiniteCNF.AbsoluteTokenCompiler.repeated emitter scalar
  let ending := endingCompiler scalar
  apply TM2ComputableInPolyTime.of_eq (TM2ListAppend.nativeComputableInPolyTime body ending)
  intro word
  simp only [FiniteCNF.tableauExpression,TransitionExpr.program_all,ofProgram_all,
    List.length_map,List.length_range,List.map_map,Function.comp_def,
    FiniteCNF.absoluteExpression_program]
  simp [List.flatMap_map,ofProgram,List.flatMap_assoc]

private def initialCompiler : TM2ComputableInPolyTime id id (fun word => ofProgram
    (FiniteCNF.absoluteExpression 0 (sourceInitialExpression verifier word).atCurrent).program) := by
  let initial := currentCompiler (FiniteNPInitializationEmitter.computableInPolyTime verifier)
  let zero : UnaryColumn.ScalarCompiler (fun _ : List encoding.Γ => 0) :=
    TM2ConstantValueCompiler.computableInPolyTime id unaryFields [0]
  apply TM2ComputableInPolyTime.of_eq (FiniteCNF.AbsoluteTokenCompiler.single initial zero)
  intro word
  simp [FiniteCNF.absoluteExpression_program,FiniteNPPaddedProgramEmitter.atCurrent_program,
    sourceInitialExpression,FiniteNPInitializationEmitter.initialProgram]

private def finalCompiler : TM2ComputableInPolyTime id id (fun word => ofProgram
    (FiniteCNF.absoluteExpression ((timePolynomial verifier).eval word.length)
      (BoundedMachineAtom.currentConfigIs (space := sourceSpace verifier word) (clockBits := 0)
        (acceptingConfiguration verifier)).atCurrent).program) := by
  let accepting := TM2ComputableInPolyTime.of_eq (acceptingComputableInPolyTime verifier .current)
    (fun word => acceptingTokens_eq verifier .current word)
  let absolute := FiniteCNF.AbsoluteTokenCompiler.single accepting (polynomialScalar (timePolynomial verifier))
  apply TM2ComputableInPolyTime.of_eq absolute
  intro word
  simp [FiniteCNF.absoluteExpression_program,FiniteNPPaddedProgramEmitter.atCurrent_program,
    BoundedMachineProgram.program_currentConfigIs,FiniteNPPaddedProgramEmitter.map_configuration]

private def wellFormedCompiler : TM2ComputableInPolyTime id id (fun word => ofProgram
    (FiniteCNF.tableauExpression (fun _ => BoundedMachineAtom.wellFormedFields
      (tm := verifier.computer.tm) (space := sourceSpace verifier word) (clockBits := 0))
      ((timePolynomial verifier).eval word.length+1)).program) := by
  let oneSlice := TM2ComputableInPolyTime.of_eq (wellFormedComputableInPolyTime verifier)
    (fun word => wellFormedTokens_eq verifier word)
  let exactSlice : TM2ComputableInPolyTime id id (fun word => ofProgram
      (BoundedMachineAtom.wellFormedFields (tm := verifier.computer.tm)
        (space := sourceSpace verifier word) (clockBits := 0)).program) :=
    TM2ComputableInPolyTime.of_eq oneSlice (fun _ => by rw [BoundedMachineProgram.program_wellFormedFields])
  exact TM2ComputableInPolyTime.of_eq
    (tableauCompiler exactSlice (polynomialScalar (timePolynomial verifier+1))) (fun word => by simp)

private def stepCompiler : TM2ComputableInPolyTime id id (fun word => ofProgram
    (FiniteCNF.tableauExpression (fun _ => FiniteMachineTrace.paddedStep verifier.computer.tm
      (sourceSpace verifier word) (acceptingConfiguration verifier))
      ((timePolynomial verifier).eval word.length)).program) := by
  let oneSlice := TM2ComputableInPolyTime.of_eq (FiniteNPPaddedProgramEmitter.computableInPolyTime verifier)
    (fun word => congrArg ofProgram (FiniteNPPaddedProgramEmitter.program_eq verifier word))
  exact tableauCompiler oneSlice (polynomialScalar (timePolynomial verifier))

/-- All four tableau blocks, together with the three outer conjunctions. -/
def programComputableInPolyTime : TM2ComputableInPolyTime id id
    (fun word => ofProgram (sourceSeparatedExpression verifier word).program) := by
  let first := TM2ListAppend.nativeComputableInPolyTime (initialCompiler verifier) (finalCompiler verifier)
  let second := TM2ListAppend.nativeComputableInPolyTime first (wellFormedCompiler verifier)
  let body := TM2ListAppend.nativeComputableInPolyTime second (stepCompiler verifier)
  let ending : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => FiniteNPInitializationEmitter.fixedEnding) :=
    TM2ConstantValueCompiler.computableInPolyTime id id FiniteNPInitializationEmitter.fixedEnding
  apply TM2ComputableInPolyTime.of_eq (TM2ListAppend.nativeComputableInPolyTime body ending)
  intro word
  simp [sourceSeparatedExpression,FiniteMachineTrace.separatedExpression,
    TransitionExpr.program_and,ofProgram_conjoin,FiniteNPInitializationEmitter.fixedEnding,List.append_assoc]

def fields (word : List encoding.Γ) : List Nat :=
  transitionCompilerInputFields (sourceSeparatedExpression verifier word)
    ((requestFreshPolynomial verifier).eval word.length)

/-- Counting and finalization produce precisely the backend's unary request. -/
def fieldsComputableInPolyTime : TM2ComputableInPolyTime id unaryFields (fields verifier) := by
  let fresh := freshCompiler (polynomialScalar (Source := encoding.Γ) (requestFreshPolynomial verifier))
  let root : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => [Token.clauseMarker]) := TM2ConstantValueCompiler.computableInPolyTime id id [Token.clauseMarker]
  let header := TM2ListAppend.nativeComputableInPolyTime fresh root
  let tokens := TM2ListAppend.nativeComputableInPolyTime header (programComputableInPolyTime verifier)
  let finalized := TM2CompositionMachine.computableInPolyTime tokens
    UnaryProgramTokenFinalizer.countAndFinalizeComputableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq finalized
  intro word
  simp only [id_eq,List.append_assoc,List.singleton_append]
  change UnaryProgramTokenFinalizer.countAndFinalize
    (requestSource ((requestFreshPolynomial verifier).eval word.length)
      (sourceSeparatedExpression verifier word).program)=unaryFields (fields verifier word)
  rw [UnaryProgramTokenFinalizer.countAndFinalize_requestSource]
  simp [fields,transitionCompilerInputFields,TransitionProgram.clauseCount,TransitionExpr.program_clauseCount]

/-- The actual source-to-request machine, in the native binary field encoding. -/
def computableInPolyTime : TM2ComputableInPolyTime encoding.encode FiniteCNFCompiler.Request.encode
    (separatedRequest verifier) := by
  let raw := TM2CompositionMachine.computableInPolyTime (fieldsComputableInPolyTime verifier)
    UnaryFieldEncoderMachine.computableInPolyTime
  refine
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := ?_ }
  intro input
  have same : FiniteCNFCompiler.Request.encode (separatedRequest verifier input)=
      PartrecToTM2.trList (fields verifier (encoding.encode input)) := by
    simp [FiniteCNFCompiler.Request.encode,FiniteCNFCompiler.Request.native,
      TransitionEvaluatorMachine.TransitionCompilerRequest.encode,separatedRequest,fields,
      sourceSeparatedExpression_atCurrent]
  simpa only [same,id_eq] using raw.outputsFun (encoding.encode input)

end LeanTrominoes.FiniteNPRequestEmitter
