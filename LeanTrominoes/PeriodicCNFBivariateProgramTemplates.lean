/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramTokenAlgebra

/-!
# Bivariate affine postorder-program templates

Clock atoms and several later bounded-machine fields are affine in one runtime
width as well as in a loop position.  This file gives the future two-counter
emitter its exact semantic target: a finite recipe language whose atom runs
have length `base + firstStride × first + secondStride × second`, together
with a compositional normalized postorder-program interface.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace BivariateProgramTemplates

open UnaryProgramTokens

/-- A natural-number atom affine in two independent runtime counters. -/
structure Atom where
  base : Nat
  firstStride : Nat
  secondStride : Nat
  deriving DecidableEq

namespace Atom

def evaluate (first second : Nat) (atom : Atom) : Nat :=
  atom.base + atom.firstStride * first + atom.secondStride * second

end Atom

/-- One finite token recipe with a bivariate affine atom-run case. -/
inductive Recipe
  | fixed (token : Token)
  | atom (base firstStride secondStride : Nat)
  deriving DecidableEq

namespace Recipe

def tokens (first second : Nat) : Recipe → List Token
  | .fixed token => [token]
  | .atom base firstStride secondStride =>
      List.replicate
        (base + firstStride * first + secondStride * second) .atomUnit

end Recipe

def positionTokens (recipes : List Recipe) (first second : Nat) :
    List Token :=
  recipes.flatMap (Recipe.tokens first second)

/-- One postorder instruction with bivariate wire atoms. -/
inductive Instruction
  | constant (value : Bool)
  | wire (slice : TransitionSlice) (atom : Atom)
  | negate
  | conjoin
  | disjoin
  deriving DecidableEq

namespace Instruction

def evaluate (first second : Nat) : Instruction → TransitionInstruction
  | .constant value => .constant value
  | .wire slice atom => .wire ⟨slice, atom.evaluate first second⟩
  | .negate => .negate
  | .conjoin => .conjoin
  | .disjoin => .disjoin

/-- Exact finite recipe block for one bivariate instruction. -/
def recipes : Instruction → List Recipe
  | .constant value =>
      [.fixed .clauseMarker, .fixed (.constant value)]
  | .wire slice atom =>
      [.fixed .clauseMarker, .fixed .clauseMarker,
        .fixed (.wireStart (ProgramTokens.sliceBool slice)),
        .atom atom.base atom.firstStride atom.secondStride,
        .fixed .atomEnd]
  | .negate =>
      [.fixed .clauseMarker, .fixed .clauseMarker, .fixed .negate]
  | .conjoin =>
      [.fixed .clauseMarker, .fixed .clauseMarker,
        .fixed .clauseMarker, .fixed .conjoin]
  | .disjoin =>
      [.fixed .clauseMarker, .fixed .clauseMarker,
        .fixed .clauseMarker, .fixed .disjoin]

@[simp]
theorem positionTokens_recipes (instruction : Instruction)
    (first second : Nat) :
    positionTokens instruction.recipes first second =
      UnaryProgramTokens.instructionTokens
        (instruction.evaluate first second) := by
  cases instruction with
  | constant value =>
      simp [recipes, evaluate, positionTokens, Recipe.tokens,
        UnaryProgramTokens.instructionTokens,
        UnaryProgramTokens.clauseTokens]
  | wire slice atom =>
      cases slice <;>
        simp [recipes, evaluate, positionTokens, Recipe.tokens,
          UnaryProgramTokens.instructionTokens,
          UnaryProgramTokens.clauseTokens, UnaryProgramTokens.atomTokens,
          Atom.evaluate, ProgramTokens.sliceBool]
  | negate =>
      simp [recipes, evaluate, positionTokens, Recipe.tokens,
        UnaryProgramTokens.instructionTokens,
        UnaryProgramTokens.clauseTokens]
  | conjoin =>
      simp [recipes, evaluate, positionTokens, Recipe.tokens,
        UnaryProgramTokens.instructionTokens,
        UnaryProgramTokens.clauseTokens]
  | disjoin =>
      simp [recipes, evaluate, positionTokens, Recipe.tokens,
        UnaryProgramTokens.instructionTokens,
        UnaryProgramTokens.clauseTokens]

end Instruction

abbrev Program := List Instruction

namespace Program

def evaluate (first second : Nat) (program : Program) :
    TransitionProgram.Program :=
  program.map (Instruction.evaluate first second)

def recipes (program : Program) : List Recipe :=
  program.flatMap Instruction.recipes

@[simp]
theorem evaluate_append (first second : Nat) (left right : Program) :
    evaluate first second (left ++ right) =
      evaluate first second left ++ evaluate first second right := by
  simp [evaluate]

@[simp]
theorem recipes_append (left right : Program) :
    recipes (left ++ right) = recipes left ++ recipes right := by
  simp [recipes]

@[simp]
theorem positionTokens_append (left right : List Recipe)
    (first second : Nat) :
    positionTokens (left ++ right) first second =
      positionTokens left first second ++
        positionTokens right first second := by
  simp [positionTokens]

@[simp]
theorem positionTokens_recipes (program : Program) (first second : Nat) :
    positionTokens program.recipes first second =
      UnaryProgramTokens.ofProgram (program.evaluate first second) := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      change positionTokens
          (instruction.recipes ++ Program.recipes program) first second =
        UnaryProgramTokens.instructionTokens
            (instruction.evaluate first second) ++
          UnaryProgramTokens.ofProgram
            (Program.evaluate first second program)
      rw [positionTokens_append, Instruction.positionTokens_recipes,
        induction]

end Program

def constant (value : Bool) : Program := [.constant value]

def wire (slice : TransitionSlice) (atom : Atom) : Program :=
  [.wire slice atom]

def current (atom : Atom) : Program := wire .current atom

def next (atom : Atom) : Program := wire .next atom

def negate (input : Program) : Program := input ++ [.negate]

def conjoin (left right : Program) : Program :=
  left ++ right ++ [.conjoin]

def disjoin (left right : Program) : Program :=
  left ++ right ++ [.disjoin]

def all : List Program → Program
  | [] => constant true
  | input :: inputs => conjoin input (all inputs)

def any : List Program → Program
  | [] => constant false
  | input :: inputs => disjoin input (any inputs)

def equal (left right : Program) : Program :=
  disjoin (conjoin left right)
    (conjoin (negate left) (negate right))

def vectorsEqual : List Atom → List Atom → Program
  | [], [] => constant true
  | left :: lefts, right :: rights =>
      conjoin (equal (current left) (next right))
        (vectorsEqual lefts rights)
  | _, _ => constant false

def binarySuccessor : List Atom → List Atom → Program
  | [], [] => constant false
  | currentAtom :: currentAtoms, nextAtom :: nextAtoms =>
      disjoin
        (conjoin
          (conjoin (negate (current currentAtom)) (next nextAtom))
          (vectorsEqual currentAtoms nextAtoms))
        (conjoin
          (conjoin (current currentAtom) (negate (next nextAtom)))
          (binarySuccessor currentAtoms nextAtoms))
  | _, _ => constant false

@[simp]
theorem evaluate_constant (value : Bool) (first second : Nat) :
    (constant value).evaluate first second =
      TransitionProgram.constant value :=
  rfl

@[simp]
theorem evaluate_wire (slice : TransitionSlice) (atom : Atom)
    (first second : Nat) :
    (wire slice atom).evaluate first second =
      TransitionProgram.wire slice (atom.evaluate first second) :=
  rfl

@[simp]
theorem evaluate_current (atom : Atom) (first second : Nat) :
    (current atom).evaluate first second =
      TransitionProgram.current (atom.evaluate first second) :=
  rfl

@[simp]
theorem evaluate_next (atom : Atom) (first second : Nat) :
    (next atom).evaluate first second =
      TransitionProgram.next (atom.evaluate first second) :=
  rfl

@[simp]
theorem evaluate_negate (input : Program) (first second : Nat) :
    (negate input).evaluate first second =
      TransitionProgram.negate (input.evaluate first second) := by
  simp [negate, TransitionProgram.negate, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_conjoin (left right : Program) (first second : Nat) :
    (conjoin left right).evaluate first second =
      TransitionProgram.conjoin (left.evaluate first second)
        (right.evaluate first second) := by
  simp [conjoin, TransitionProgram.conjoin, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_disjoin (left right : Program) (first second : Nat) :
    (disjoin left right).evaluate first second =
      TransitionProgram.disjoin (left.evaluate first second)
        (right.evaluate first second) := by
  simp [disjoin, TransitionProgram.disjoin, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_all (inputs : List Program) (first second : Nat) :
    (all inputs).evaluate first second =
      TransitionProgram.all
        (inputs.map (Program.evaluate first second)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs induction =>
      simp [all, TransitionProgram.all, induction]

@[simp]
theorem evaluate_any (inputs : List Program) (first second : Nat) :
    (any inputs).evaluate first second =
      TransitionProgram.any
        (inputs.map (Program.evaluate first second)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs induction =>
      simp [any, TransitionProgram.any, induction]

@[simp]
theorem evaluate_equal (left right : Program) (first second : Nat) :
    (equal left right).evaluate first second =
      TransitionProgram.equal (left.evaluate first second)
        (right.evaluate first second) := by
  simp [equal, TransitionProgram.equal]

@[simp]
theorem evaluate_vectorsEqual (left right : List Atom)
    (first second : Nat) :
    (vectorsEqual left right).evaluate first second =
      TransitionProgram.vectorsEqual
        (left.map (Atom.evaluate first second))
        (right.map (Atom.evaluate first second)) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons left lefts induction =>
      cases right with
      | nil => rfl
      | cons right rights =>
          simp [vectorsEqual, TransitionProgram.vectorsEqual, induction]

@[simp]
theorem evaluate_binarySuccessor (currentAtoms nextAtoms : List Atom)
    (first second : Nat) :
    (binarySuccessor currentAtoms nextAtoms).evaluate first second =
      TransitionProgram.binarySuccessor
        (currentAtoms.map (Atom.evaluate first second))
        (nextAtoms.map (Atom.evaluate first second)) := by
  induction currentAtoms generalizing nextAtoms with
  | nil => cases nextAtoms <;> rfl
  | cons currentAtom currentAtoms induction =>
      cases nextAtoms with
      | nil => rfl
      | cons nextAtom nextAtoms =>
          simp [binarySuccessor, TransitionProgram.binarySuccessor,
            induction]

end BivariateProgramTemplates
end PeriodicCNF
end LeanTrominoes
