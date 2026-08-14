/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryCountPaddingMachine
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFTransitionProgramVectors

/-!
# Finite tokens for streaming compact transition programs

The postorder instruction type contains an unbounded natural atom payload and
is therefore not a finite machine alphabet.  This file factors each wire into
a finite wire-start token, its canonical native binary symbols, and a finite
field-end token.  All other instructions are single finite tokens.

Each instruction also carries one, two, or three ignored clause-marker tokens.
Their count is exactly the compiler clause count, so the generic verified
binary-count padding machine can later materialize the request header without
parsing the instruction stream.  Dropping those markers and expanding every
remaining token is a fixed finite block transduction, proved to equal the
native `trList` encoding of the compact postorder fields.
-/

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ProgramTokens

/-- Finite streaming alphabet for compact postorder instructions. -/
inductive Token
  | clauseMarker
  | constant (value : Bool)
  | wireStart (nextSlice : Bool)
  | atomSymbol (symbol : PartrecToTM2.Γ')
  | atomEnd
  | freshSymbol (symbol : PartrecToTM2.Γ')
  | freshEnd
  | negate
  | conjoin
  | disjoin
  deriving DecidableEq, Fintype, Inhabited

def sliceBool : TransitionSlice → Bool
  | .current => false
  | .next => true

def sliceField : TransitionSlice → Nat
  | .current => 0
  | .next => 1

@[simp]
theorem sliceBool_eq_true_iff (slice : TransitionSlice) :
    sliceBool slice = true ↔ slice = .next := by
  cases slice <;> simp [sliceBool]

@[simp]
theorem sliceField_eq_if (slice : TransitionSlice) :
    sliceField slice = if sliceBool slice then 1 else 0 := by
  cases slice <;> rfl

def clauseTokens (count : Nat) : List Token :=
  List.replicate count .clauseMarker

def atomTokens (atom : Nat) : List Token :=
  (PartrecToTM2.trNat atom).map Token.atomSymbol

/-- Finite token block for one postorder instruction. -/
def instructionTokens : TransitionInstruction → List Token
  | .constant value =>
      clauseTokens 1 ++ [.constant value]
  | .wire input =>
      clauseTokens 2 ++ [.wireStart (sliceBool input.slice)] ++
        atomTokens input.atom ++ [.atomEnd]
  | .negate =>
      clauseTokens 2 ++ [.negate]
  | .conjoin =>
      clauseTokens 3 ++ [.conjoin]
  | .disjoin =>
      clauseTokens 3 ++ [.disjoin]

/-- Token stream of a complete compact postorder program. -/
def ofProgram (program : List TransitionInstruction) : List Token :=
  program.flatMap instructionTokens

/-- Select only the ignored clause-weight markers. -/
def isClauseMarker : Token → Bool
  | .clauseMarker => true
  | _ => false

/-- Native block emitted by one finite token.  Atom symbols are copied, while
`atomEnd` supplies the delimiter completing a wire's atom field. -/
def nativeBlock : Token → List PartrecToTM2.Γ'
  | .clauseMarker => []
  | .constant value =>
      PartrecToTM2.trList [0, if value then 1 else 0]
  | .wireStart nextSlice =>
      PartrecToTM2.trList [1, if nextSlice then 1 else 0]
  | .atomSymbol symbol => [symbol]
  | .atomEnd => [.cons]
  | .freshSymbol symbol => [symbol]
  | .freshEnd => [.cons]
  | .negate => PartrecToTM2.trList [2]
  | .conjoin => PartrecToTM2.trList [3]
  | .disjoin => PartrecToTM2.trList [4]

/-- Native word obtained by fixed block expansion of a token stream. -/
def nativeEncode (tokens : List Token) : List PartrecToTM2.Γ' :=
  tokens.flatMap nativeBlock

@[simp]
theorem nativeBlock_clauseMarker :
    nativeBlock .clauseMarker = [] :=
  rfl

@[simp]
theorem nativeEncode_nil : nativeEncode [] = [] :=
  rfl

@[simp]
theorem nativeEncode_cons (token : Token) (tokens : List Token) :
    nativeEncode (token :: tokens) =
      nativeBlock token ++ nativeEncode tokens :=
  rfl

@[simp]
theorem nativeEncode_append (first second : List Token) :
    nativeEncode (first ++ second) =
      nativeEncode first ++ nativeEncode second := by
  simp [nativeEncode]

@[simp]
theorem nativeEncode_clauseTokens (count : Nat) :
    nativeEncode (clauseTokens count) = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [clauseTokens, nativeEncode, nativeBlock]

@[simp]
theorem nativeEncode_clausePrefix (count : Nat) (tokens : List Token) :
    nativeEncode (clauseTokens count ++ tokens) = nativeEncode tokens := by
  rw [nativeEncode_append, nativeEncode_clauseTokens]
  rfl

@[simp]
theorem nativeEncode_atomTokens (atom : Nat) :
    nativeEncode (atomTokens atom) = PartrecToTM2.trNat atom := by
  unfold atomTokens nativeEncode
  induction PartrecToTM2.trNat atom with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [nativeBlock, induction]

@[simp]
theorem nativeEncode_instructionTokens
    (instruction : TransitionInstruction) :
    nativeEncode (instructionTokens instruction) =
      PartrecToTM2.trList instruction.fields := by
  cases instruction with
  | constant value =>
      rw [instructionTokens, nativeEncode_clausePrefix]
      simp [nativeEncode, nativeBlock, TransitionInstruction.fields]
  | wire input =>
      rcases input with ⟨slice, atom⟩
      cases slice <;>
        simp [instructionTokens, TransitionInstruction.fields,
          nativeEncode_append, nativeBlock, sliceBool,
          PartrecToTM2.trList]
  | negate =>
      rw [instructionTokens, nativeEncode_clausePrefix]
      rfl
  | conjoin =>
      rw [instructionTokens, nativeEncode_clausePrefix]
      rfl
  | disjoin =>
      rw [instructionTokens, nativeEncode_clausePrefix]
      rfl

theorem trList_append (first second : List Nat) :
    PartrecToTM2.trList (first ++ second) =
      PartrecToTM2.trList first ++ PartrecToTM2.trList second := by
  induction first with
  | nil => rfl
  | cons field fields induction =>
      simp [PartrecToTM2.trList, induction, List.append_assoc]

/-- Fixed token expansion is exactly the evaluator-native encoding of the
compact natural instruction fields. -/
@[simp]
theorem nativeEncode_ofProgram (program : List TransitionInstruction) :
    nativeEncode (ofProgram program) =
      PartrecToTM2.trList (transitionProgramFields program) := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
          instructionTokens instruction ++ ofProgram program by rfl,
        nativeEncode_append, nativeEncode_instructionTokens, induction]
      rw [show transitionProgramFields (instruction :: program) =
          instruction.fields ++ transitionProgramFields program by rfl,
        trList_append]

theorem selectedCount_append (first second : List Token) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
        (first ++ second) =
      BinaryCountPaddingMachine.selectedCount isClauseMarker first +
        BinaryCountPaddingMachine.selectedCount isClauseMarker second := by
  induction first with
  | nil => simp [BinaryCountPaddingMachine.selectedCount]
  | cons token tokens induction =>
      simp only [List.cons_append,
        BinaryCountPaddingMachine.selectedCount_cons, induction]
      omega

@[simp]
theorem selectedCount_clauseTokens (count : Nat) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (clauseTokens count) = count := by
  unfold clauseTokens
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [BinaryCountPaddingMachine.selectedCount,
        isClauseMarker, induction]
      omega

@[simp]
theorem selectedCount_atomTokens (atom : Nat) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (atomTokens atom) = 0 := by
  unfold atomTokens
  induction PartrecToTM2.trNat atom with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [isClauseMarker, induction]

/-- Tagged native field carrying the request's initial fresh atom.  Separate
constructors keep it distinguishable from wire payloads for the final header
rotation machine. -/
def freshTokens (fresh : Nat) : List Token :=
  (PartrecToTM2.trNat fresh).map Token.freshSymbol ++ [.freshEnd]

@[simp]
theorem nativeEncode_map_freshSymbol
    (symbols : List PartrecToTM2.Γ') :
    nativeEncode (symbols.map Token.freshSymbol) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [nativeBlock, induction]

@[simp]
theorem nativeEncode_freshTokens (fresh : Nat) :
    nativeEncode (freshTokens fresh) =
      PartrecToTM2.trNat fresh ++ [.cons] := by
  simp [freshTokens, nativeBlock]

@[simp]
theorem selectedCount_map_freshSymbol
    (symbols : List PartrecToTM2.Γ') :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (symbols.map Token.freshSymbol) = 0 := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [isClauseMarker, induction]

@[simp]
theorem selectedCount_freshTokens (fresh : Nat) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (freshTokens fresh) = 0 := by
  simp [freshTokens, selectedCount_append,
    BinaryCountPaddingMachine.selectedCount, isClauseMarker]

@[simp]
theorem selectedCount_instructionTokens
    (instruction : TransitionInstruction) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (instructionTokens instruction) = instruction.clauseCount := by
  cases instruction with
  | constant value =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, BinaryCountPaddingMachine.selectedCount,
        isClauseMarker]
  | wire input =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, BinaryCountPaddingMachine.selectedCount,
        isClauseMarker]
  | negate =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, BinaryCountPaddingMachine.selectedCount,
        isClauseMarker]
  | conjoin =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, BinaryCountPaddingMachine.selectedCount,
        isClauseMarker]
  | disjoin =>
      simp [instructionTokens, TransitionInstruction.clauseCount,
        selectedCount_append, BinaryCountPaddingMachine.selectedCount,
        isClauseMarker]

/-- Clause-marker count is exactly the instruction-derived compiler clause
count. -/
@[simp]
theorem selectedCount_ofProgram (program : List TransitionInstruction) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (ofProgram program) = TransitionProgram.clauseCount program := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
        instructionTokens instruction ++ ofProgram program by rfl,
        selectedCount_append, selectedCount_instructionTokens, induction]
      simp [TransitionProgram.clauseCount]

/-- Source word handed to the clause-count materializer.  Its native image is
the fresh field followed by the compact program; the extra root marker is
ignored by native expansion but contributes the final forced-root clause. -/
def requestSource (fresh : Nat)
    (program : List TransitionInstruction) : List Token :=
  freshTokens fresh ++ .clauseMarker :: ofProgram program

@[simp]
theorem nativeEncode_requestSource (fresh : Nat)
    (program : List TransitionInstruction) :
    nativeEncode (requestSource fresh program) =
      PartrecToTM2.trNat fresh ++ [.cons] ++
        PartrecToTM2.trList (transitionProgramFields program) := by
  simp [requestSource, List.append_assoc]

@[simp]
theorem selectedCount_requestSource (fresh : Nat)
    (program : List TransitionInstruction) :
    BinaryCountPaddingMachine.selectedCount isClauseMarker
      (requestSource fresh program) =
        TransitionProgram.clauseCount program + 1 := by
  rw [requestSource, selectedCount_append, selectedCount_freshTokens,
    BinaryCountPaddingMachine.selectedCount_cons,
    selectedCount_ofProgram]
  simp [isClauseMarker]
  omega

/-- Retain the token source word and append the exact undelimited native
binary clause header. -/
def countedRequest (fresh : Nat)
    (program : List TransitionInstruction) :
    List (Token ⊕ PartrecToTM2.Γ') :=
  BinaryCountPaddingMachine.paddedOutput isClauseMarker
    (requestSource fresh program)

@[simp]
theorem countedRequest_eq (fresh : Nat)
    (program : List TransitionInstruction) :
    countedRequest fresh program =
      (requestSource fresh program).map
          (fun token => Sum.inl token) ++
        (PartrecToTM2.trNat
          (TransitionProgram.clauseCount program + 1)).map
            (fun symbol => Sum.inr symbol) := by
  simp [countedRequest, BinaryCountPaddingMachine.paddedOutput]

/-- Appending an exact native clause count to an arbitrary token word is
polynomial-time. -/
noncomputable def appendClauseCountComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List (Token ⊕ PartrecToTM2.Γ'))
      Token (Token ⊕ PartrecToTM2.Γ') id id
      (BinaryCountPaddingMachine.paddedOutput isClauseMarker) :=
  BinaryCountPaddingMachine.computableInPolyTime isClauseMarker

/-- Dropping markers and expanding finite tokens to native symbols is
polynomial-time (indeed linear-time). -/
noncomputable def nativeEncodeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List PartrecToTM2.Γ')
      Token PartrecToTM2.Γ' id id nativeEncode :=
  FiniteBlockTransducer.computableInPolyTime nativeBlock

end ProgramTokens
end PeriodicCNF
end LeanTrominoes
