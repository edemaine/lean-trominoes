/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldEncoderMachine
import LeanTrominoes.UnaryPolynomialPaddingMachine
import LeanTrominoes.PeriodicCNFProgramTokens

/-!
# Finite unary tokens for the compact transition-program printer

The concrete request printer must generate arbitrary runtime atom numbers
using a fixed finite alphabet.  This file therefore replaces every native
binary atom payload by a unary run.  Fixed instruction tags remain finite
tokens, and ignored clause markers retain their exact Tseitin weights.

A fixed block expansion turns the stream into delimiter-terminated unary
natural fields.  A subsequent `UnaryFieldEncoderMachine` pass converts those
fields to the evaluator's canonical native binary representation.  Counting
the clause markers is already supplied by the verified unary Horner machine.
-/

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace UnaryProgramTokens

open UnaryFieldEncoderMachine

/-- Finite output alphabet of the counter-driven instruction emitter. -/
inductive Token
  | clauseMarker
  | constant (value : Bool)
  | wireStart (nextSlice : Bool)
  | atomUnit
  | atomEnd
  | freshUnit
  | freshEnd
  | negate
  | conjoin
  | disjoin
  deriving DecidableEq, Fintype, Inhabited

def clauseTokens (count : Nat) : List Token :=
  List.replicate count .clauseMarker

def atomTokens (atom : Nat) : List Token :=
  List.replicate atom .atomUnit

def freshTokens (fresh : Nat) : List Token :=
  List.replicate fresh .freshUnit ++ [.freshEnd]

/-- Unary finite-token block for one compact postorder instruction. -/
def instructionTokens : TransitionInstruction → List Token
  | .constant value =>
      clauseTokens 1 ++ [.constant value]
  | .wire input =>
      clauseTokens 2 ++
        [.wireStart (ProgramTokens.sliceBool input.slice)] ++
        atomTokens input.atom ++ [.atomEnd]
  | .negate =>
      clauseTokens 2 ++ [.negate]
  | .conjoin =>
      clauseTokens 3 ++ [.conjoin]
  | .disjoin =>
      clauseTokens 3 ++ [.disjoin]

/-- Unary finite-token stream of a complete compact postorder program. -/
def ofProgram (program : TransitionProgram.Program) : List Token :=
  program.flatMap instructionTokens

/-- Select precisely the ignored Tseitin clause-weight tokens. -/
def isClauseMarker : Token → Bool
  | .clauseMarker => true
  | _ => false

/-- Fixed unary-field block represented by one token. -/
def unaryBlock : Token → List Symbol
  | .clauseMarker => []
  | .constant value =>
      unaryFields [0, if value then 1 else 0]
  | .wireStart nextSlice =>
      unaryFields [1, if nextSlice then 1 else 0]
  | .atomUnit => [.unit]
  | .atomEnd => [.delimiter]
  | .freshUnit => [.unit]
  | .freshEnd => [.delimiter]
  | .negate => unaryFields [2]
  | .conjoin => unaryFields [3]
  | .disjoin => unaryFields [4]

/-- Expand a finite token stream into delimiter-terminated unary fields. -/
def unaryEncode (tokens : List Token) : List Symbol :=
  tokens.flatMap unaryBlock

@[simp]
theorem unaryEncode_nil : unaryEncode [] = [] :=
  rfl

@[simp]
theorem unaryEncode_cons (token : Token) (tokens : List Token) :
    unaryEncode (token :: tokens) =
      unaryBlock token ++ unaryEncode tokens :=
  rfl

@[simp]
theorem unaryEncode_append (first second : List Token) :
    unaryEncode (first ++ second) =
      unaryEncode first ++ unaryEncode second := by
  simp [unaryEncode]

@[simp]
theorem unaryFields_append (first second : List Nat) :
    unaryFields (first ++ second) =
      unaryFields first ++ unaryFields second := by
  simp [unaryFields]

@[simp]
theorem unaryEncode_clauseTokens (count : Nat) :
    unaryEncode (clauseTokens count) = [] := by
  simp [clauseTokens, unaryEncode, unaryBlock]

@[simp]
theorem unaryEncode_clausePrefix (count : Nat) (tokens : List Token) :
    unaryEncode (clauseTokens count ++ tokens) = unaryEncode tokens := by
  rw [unaryEncode_append, unaryEncode_clauseTokens]
  rfl

@[simp]
theorem unaryEncode_replicate_atomUnit (count : Nat) :
    unaryEncode (List.replicate count .atomUnit) =
      List.replicate count .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, unaryEncode_cons, unaryBlock,
        List.replicate_succ, induction]
      rfl

@[simp]
theorem unaryEncode_atomTokens (atom : Nat) :
    unaryEncode (atomTokens atom) = List.replicate atom .unit := by
  exact unaryEncode_replicate_atomUnit atom

@[simp]
theorem unaryEncode_replicate_freshUnit (count : Nat) :
    unaryEncode (List.replicate count .freshUnit) =
      List.replicate count .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, unaryEncode_cons, unaryBlock,
        List.replicate_succ, induction]
      rfl

@[simp]
theorem unaryEncode_freshTokens (fresh : Nat) :
    unaryEncode (freshTokens fresh) = unaryField fresh := by
  simp [freshTokens, unaryField, unaryBlock]

/-- Fixed expansion of each finite unary instruction block is exactly its
natural-field representation. -/
@[simp]
theorem unaryEncode_instructionTokens
    (instruction : TransitionInstruction) :
    unaryEncode (instructionTokens instruction) =
      unaryFields instruction.fields := by
  cases instruction with
  | constant value =>
      cases value <;>
        simp [instructionTokens, unaryBlock,
          TransitionInstruction.fields]
  | wire input =>
      rcases input with ⟨slice, atom⟩
      cases slice <;>
        simp [instructionTokens, unaryBlock, atomTokens, unaryField,
          unaryFields, ProgramTokens.sliceBool,
          TransitionInstruction.fields, List.append_assoc]
  | negate =>
      simp [instructionTokens, unaryBlock, TransitionInstruction.fields]
  | conjoin =>
      simp [instructionTokens, unaryBlock, TransitionInstruction.fields]
  | disjoin =>
      simp [instructionTokens, unaryBlock, TransitionInstruction.fields]

/-- Expanding a whole unary-token program gives exactly the corresponding
sequence of unary natural fields. -/
@[simp]
theorem unaryEncode_ofProgram (program : TransitionProgram.Program) :
    unaryEncode (ofProgram program) =
      unaryFields (transitionProgramFields program) := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
          instructionTokens instruction ++ ofProgram program by rfl,
        unaryEncode_append, unaryEncode_instructionTokens, induction]
      rw [show transitionProgramFields (instruction :: program) =
          instruction.fields ++ transitionProgramFields program by rfl,
        unaryFields_append]

theorem selectedCount_append (first second : List Token) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
        (first ++ second) =
      UnaryPolynomialPaddingMachine.selectedCount isClauseMarker first +
        UnaryPolynomialPaddingMachine.selectedCount isClauseMarker second := by
  induction first with
  | nil => simp [UnaryPolynomialPaddingMachine.selectedCount]
  | cons token tokens induction =>
      simp only [List.cons_append,
        UnaryPolynomialPaddingMachine.selectedCount_cons, induction]
      omega

@[simp]
theorem selectedCount_clauseTokens (count : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (clauseTokens count) = count := by
  unfold clauseTokens
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker, induction]
      omega

@[simp]
theorem selectedCount_replicate_atomUnit (count : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (List.replicate count .atomUnit) = 0 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker, induction]

@[simp]
theorem selectedCount_atomTokens (atom : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (atomTokens atom) = 0 := by
  exact selectedCount_replicate_atomUnit atom

@[simp]
theorem selectedCount_replicate_freshUnit (count : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (List.replicate count .freshUnit) = 0 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker, induction]

@[simp]
theorem selectedCount_freshTokens (fresh : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (freshTokens fresh) = 0 := by
  rw [freshTokens, selectedCount_append,
    selectedCount_replicate_freshUnit]
  simp [UnaryPolynomialPaddingMachine.selectedCount, isClauseMarker]

@[simp]
theorem selectedCount_instructionTokens
    (instruction : TransitionInstruction) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (instructionTokens instruction) = instruction.clauseCount := by
  cases instruction with
  | constant value =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker]
  | wire input =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker]
  | negate =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker]
  | conjoin =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker]
  | disjoin =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, UnaryPolynomialPaddingMachine.selectedCount,
        isClauseMarker]

@[simp]
theorem selectedCount_ofProgram (program : TransitionProgram.Program) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (ofProgram program) = TransitionProgram.clauseCount program := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
          instructionTokens instruction ++ ofProgram program by rfl,
        selectedCount_append, selectedCount_instructionTokens, induction]
      simp [TransitionProgram.clauseCount]

/-- Finite stream the concrete emitter must produce.  The fresh boundary is
unary, and the extra root marker contributes the evaluator's forced-root
clause without producing a program field. -/
def requestSource (fresh : Nat)
    (program : TransitionProgram.Program) : List Token :=
  freshTokens fresh ++ .clauseMarker :: ofProgram program

@[simp]
theorem unaryEncode_requestSource (fresh : Nat)
    (program : TransitionProgram.Program) :
    unaryEncode (requestSource fresh program) =
      unaryField fresh ++
        unaryFields (transitionProgramFields program) := by
  simp [requestSource, unaryBlock]

@[simp]
theorem selectedCount_requestSource (fresh : Nat)
    (program : TransitionProgram.Program) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (requestSource fresh program) =
        TransitionProgram.clauseCount program + 1 := by
  rw [requestSource, selectedCount_append, selectedCount_freshTokens,
    UnaryPolynomialPaddingMachine.selectedCount_cons,
    selectedCount_ofProgram]
  simp [isClauseMarker]
  omega

/-- Retain a unary token request and append one unary unit for every exact
clause marker.  Coefficients `[0, 1]` implement the identity polynomial. -/
def countedRequest (fresh : Nat)
    (program : TransitionProgram.Program) : List (Token ⊕ Unit) :=
  UnaryPolynomialPaddingMachine.paddedOutput isClauseMarker [0, 1]
    (requestSource fresh program)

@[simp]
theorem evalCoefficients_identity (count : Nat) :
    UnaryPolynomialPaddingMachine.evalCoefficients [0, 1] count = count := by
  simp [UnaryPolynomialPaddingMachine.evalCoefficients]

@[simp]
theorem countedRequest_eq (fresh : Nat)
    (program : TransitionProgram.Program) :
    countedRequest fresh program =
      (requestSource fresh program).map Sum.inl ++
        List.replicate (TransitionProgram.clauseCount program + 1)
          (Sum.inr ()) := by
  simp [countedRequest, UnaryPolynomialPaddingMachine.paddedOutput]

/-- Appending the exact unary clause count to an arbitrary finite token word
is polynomial-time. -/
noncomputable def appendClauseCountComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List (Token ⊕ Unit)) Token (Token ⊕ Unit)
      id id
      (UnaryPolynomialPaddingMachine.paddedOutput isClauseMarker [0, 1]) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime isClauseMarker [0, 1]

/-- Fixed token expansion to delimiter-terminated unary fields is
polynomial-time (indeed linear-time). -/
noncomputable def unaryEncodeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List Symbol) Token Symbol id id unaryEncode :=
  FiniteBlockTransducer.computableInPolyTime unaryBlock

end UnaryProgramTokens
end PeriodicCNF
end LeanTrominoes
