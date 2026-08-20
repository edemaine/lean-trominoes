/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseArityData

/-!
# Finite clause profiles of unary transition programs

Besides arity, the strip geometry needs each literal's polarity and whether
it reads the current or next horizontal slice.  Both pieces of data are
finite, so the exact generated clause sequence remains a fixed block scan of
the uniform unary-program stream.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace UnaryProgramClauseProfile

open UnaryProgramTokens

/-- Route-relevant data of one generated literal. -/
structure LiteralProfile where
  nextSlice : Bool
  value : Bool
  deriving DecidableEq, Fintype, Inhabited

/-- Every clause produced by the transition compiler is nonempty and has
width at most three. -/
inductive ClauseProfile
  | unary (first : LiteralProfile)
  | binary (first second : LiteralProfile)
  | ternary (first second third : LiteralProfile)
  deriving DecidableEq, Fintype

instance : Inhabited ClauseProfile :=
  ⟨.unary ⟨false, false⟩⟩

def current (value : Bool) : LiteralProfile :=
  ⟨false, value⟩

def input (nextSlice value : Bool) : LiteralProfile :=
  ⟨nextSlice, value⟩

def ClauseProfile.literals : ClauseProfile → List LiteralProfile
  | .unary first => [first]
  | .binary first second => [first, second]
  | .ternary first second third => [first, second, third]

def ClauseProfile.arity : ClauseProfile → UnaryProgramClauseArity.Arity
  | .unary _ => .unary
  | .binary _ _ => .binary
  | .ternary _ _ _ => .ternary

/-- Exact clause profiles emitted by one postorder instruction. -/
def instructionProfiles : TransitionInstruction → List ClauseProfile
  | .constant value =>
      [.unary (current value)]
  | .wire wire =>
      [.binary (current false)
          (input (ProgramTokens.sliceBool wire.slice) true),
        .binary (current true)
          (input (ProgramTokens.sliceBool wire.slice) false)]
  | .negate =>
      [.binary (current false) (current false),
        .binary (current true) (current true)]
  | .conjoin =>
      [.binary (current false) (current true),
        .binary (current false) (current true),
        .ternary (current true) (current false) (current false)]
  | .disjoin =>
      [.binary (current true) (current false),
        .binary (current true) (current false),
        .ternary (current false) (current true) (current true)]

/-- Recognize instruction tags while ignoring unary numeric payloads and
clause-count markers. -/
def tokenBlock : Token → List ClauseProfile
  | .constant value => instructionProfiles (.constant value)
  | .wireStart nextSlice =>
      instructionProfiles (.wire
        ⟨if nextSlice then .next else .current, 0⟩)
  | .negate => instructionProfiles .negate
  | .conjoin => instructionProfiles .conjoin
  | .disjoin => instructionProfiles .disjoin
  | _ => []

def programScan (tokens : List Token) : List ClauseProfile :=
  tokens.flatMap tokenBlock

/-- Append the forced-root positive current-slice unit clause. -/
def requestScan (tokens : List Token) : List ClauseProfile :=
  programScan tokens ++ [.unary (current true)]

@[simp] theorem programScan_append (first second : List Token) :
    programScan (first ++ second) =
      programScan first ++ programScan second := by
  simp [programScan]

@[simp] theorem programScan_instructionTokens
    (instruction : TransitionInstruction) :
    programScan (instructionTokens instruction) =
      instructionProfiles instruction := by
  cases instruction with
  | constant value =>
      cases value <;>
        simp [instructionTokens, clauseTokens, programScan, tokenBlock,
          instructionProfiles]
  | wire wire =>
      rcases wire with ⟨slice, atom⟩
      cases slice <;>
        simp [instructionTokens, clauseTokens, atomTokens, programScan,
          tokenBlock, instructionProfiles, ProgramTokens.sliceBool]
  | negate =>
      simp [instructionTokens, clauseTokens, programScan, tokenBlock,
        instructionProfiles]
  | conjoin =>
      simp [instructionTokens, clauseTokens, programScan, tokenBlock,
        instructionProfiles]
  | disjoin =>
      simp [instructionTokens, clauseTokens, programScan, tokenBlock,
        instructionProfiles]

@[simp] theorem programScan_ofProgram
    (program : TransitionProgram.Program) :
    programScan (ofProgram program) =
      program.flatMap instructionProfiles := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
          instructionTokens instruction ++ ofProgram program by rfl,
        programScan_append, programScan_instructionTokens, induction]
      rfl

@[simp] theorem requestScan_requestSource
    (fresh : Nat) (program : TransitionProgram.Program) :
    requestScan (requestSource fresh program) =
      program.flatMap instructionProfiles ++
        [.unary (current true)] := by
  unfold requestScan requestSource
  rw [programScan_append]
  rw [show programScan (.clauseMarker :: ofProgram program) =
      programScan (ofProgram program) by rfl,
    programScan_ofProgram]
  simp [freshTokens, programScan, tokenBlock]

@[simp] theorem instructionProfiles_map_arity
    (instruction : TransitionInstruction) :
    (instructionProfiles instruction).map ClauseProfile.arity =
      UnaryProgramClauseArity.instructionArities instruction := by
  cases instruction with
  | constant value => rfl
  | wire wire => rfl
  | negate => rfl
  | conjoin => rfl
  | disjoin => rfl

/-- Forgetting route data recovers the previously certified arity scan. -/
@[simp] theorem requestScan_map_arity (tokens : List Token) :
    (requestScan tokens).map ClauseProfile.arity =
      UnaryProgramClauseArity.requestScan tokens := by
  unfold requestScan UnaryProgramClauseArity.requestScan
  rw [List.map_append]
  congr 1
  unfold programScan UnaryProgramClauseArity.programScan
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp only [List.flatMap_cons, List.map_append, induction]
      cases token <;> rfl

end UnaryProgramClauseProfile
end PeriodicCNF
end LeanTrominoes
