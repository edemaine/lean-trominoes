/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineTemplateEmitterTime

/-!
# Affine postorder-program templates

This file gives the reusable affine emitter a program-level interface.  A
wire atom is represented by fixed `base` and `stride` coefficients; evaluating
at a position recovers an ordinary transition instruction, while translating
to emitter recipes recovers its complete unary token block exactly.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace AffineProgramTemplates

open AffineTemplateEmitterMachine
open UnaryProgramTokens

/-- A natural-number atom affine in one zero-based runtime position. -/
structure Atom where
  base : Nat
  stride : Nat
  deriving DecidableEq

namespace Atom

def evaluate (position : Nat) (atom : Atom) : Nat :=
  atom.base + atom.stride * position

end Atom

/-- One postorder instruction with affine wire atoms. -/
inductive Instruction
  | constant (value : Bool)
  | wire (slice : TransitionSlice) (atom : Atom)
  | negate
  | conjoin
  | disjoin
  deriving DecidableEq

namespace Instruction

def evaluate (position : Nat) : Instruction → TransitionInstruction
  | .constant value => .constant value
  | .wire slice atom => .wire ⟨slice, atom.evaluate position⟩
  | .negate => .negate
  | .conjoin => .conjoin
  | .disjoin => .disjoin

/-- Exact finite recipe block for one affine instruction. -/
def recipes : Instruction → List Recipe
  | .constant value =>
      [.fixed .clauseMarker, .fixed (.constant value)]
  | .wire slice atom =>
      [.fixed .clauseMarker, .fixed .clauseMarker,
        .fixed (.wireStart (ProgramTokens.sliceBool slice)),
        .atom atom.base atom.stride, .fixed .atomEnd]
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
    (position : Nat) :
    positionTokens instruction.recipes position =
      instructionTokens (instruction.evaluate position) := by
  cases instruction with
  | constant value => simp [recipes, evaluate, positionTokens,
      Recipe.tokens, instructionTokens, clauseTokens]
  | wire slice atom =>
      cases slice <;>
        simp [recipes, evaluate, positionTokens, Recipe.tokens,
          instructionTokens, clauseTokens, atomTokens, Atom.evaluate,
          ProgramTokens.sliceBool]
  | negate => simp [recipes, evaluate, positionTokens, Recipe.tokens,
      instructionTokens, clauseTokens]
  | conjoin => simp [recipes, evaluate, positionTokens, Recipe.tokens,
      instructionTokens, clauseTokens]
  | disjoin => simp [recipes, evaluate, positionTokens, Recipe.tokens,
      instructionTokens, clauseTokens]

end Instruction

abbrev Program := List Instruction

namespace Program

def evaluate (position : Nat) (program : Program) :
    TransitionProgram.Program :=
  program.map (Instruction.evaluate position)

def recipes (program : Program) : List Recipe :=
  program.flatMap Instruction.recipes

@[simp]
theorem evaluate_append (position : Nat) (first second : Program) :
    evaluate position (first ++ second) =
      evaluate position first ++ evaluate position second := by
  simp [evaluate]

@[simp]
theorem recipes_append (first second : Program) :
    recipes (first ++ second) = recipes first ++ recipes second := by
  simp [recipes]

@[simp]
theorem positionTokens_append (first second : List Recipe) (position : Nat) :
    positionTokens (first ++ second) position =
      positionTokens first position ++ positionTokens second position := by
  simp [positionTokens]

@[simp]
theorem positionTokens_recipes (program : Program) (position : Nat) :
    positionTokens program.recipes position =
      ofProgram (program.evaluate position) := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      change positionTokens
          (instruction.recipes ++ Program.recipes program) position =
        instructionTokens (instruction.evaluate position) ++
          ofProgram (Program.evaluate position program)
      rw [positionTokens_append, Instruction.positionTokens_recipes,
        induction]

end Program

def constant (value : Bool) : Program := [.constant value]

def wire (slice : TransitionSlice) (atom : Atom) : Program :=
  [.wire slice atom]

def current (atom : Atom) : Program := wire .current atom

def next (atom : Atom) : Program := wire .next atom

def negate (input : Program) : Program := input ++ [.negate]

def conjoin (first second : Program) : Program :=
  first ++ second ++ [.conjoin]

def disjoin (first second : Program) : Program :=
  first ++ second ++ [.disjoin]

def all : List Program → Program
  | [] => constant true
  | input :: inputs => conjoin input (all inputs)

def any : List Program → Program
  | [] => constant false
  | input :: inputs => disjoin input (any inputs)

def equal (first second : Program) : Program :=
  disjoin (conjoin first second)
    (conjoin (negate first) (negate second))

def vectorsEqual : List Atom → List Atom → Program
  | [], [] => constant true
  | first :: firsts, second :: seconds =>
      conjoin (equal (current first) (next second))
        (vectorsEqual firsts seconds)
  | _, _ => constant false

def exactlyOne : List Program → Program
  | [] => constant false
  | input :: inputs =>
      disjoin
        (conjoin input (all (inputs.map negate)))
        (conjoin (negate input) (exactlyOne inputs))

def currentExactlyOne (atoms : List Atom) : Program :=
  exactlyOne (atoms.map current)

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
theorem evaluate_constant (value : Bool) (position : Nat) :
    (constant value).evaluate position = TransitionProgram.constant value :=
  rfl

@[simp]
theorem evaluate_wire (slice : TransitionSlice) (atom : Atom)
    (position : Nat) :
    (wire slice atom).evaluate position =
      TransitionProgram.wire slice (atom.evaluate position) :=
  rfl

@[simp]
theorem evaluate_current (atom : Atom) (position : Nat) :
    (current atom).evaluate position =
      TransitionProgram.current (atom.evaluate position) :=
  rfl

@[simp]
theorem evaluate_next (atom : Atom) (position : Nat) :
    (next atom).evaluate position =
      TransitionProgram.next (atom.evaluate position) :=
  rfl

@[simp]
theorem evaluate_negate (input : Program) (position : Nat) :
    (negate input).evaluate position =
      TransitionProgram.negate (input.evaluate position) := by
  simp [negate, TransitionProgram.negate, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_conjoin (first second : Program) (position : Nat) :
    (conjoin first second).evaluate position =
      TransitionProgram.conjoin (first.evaluate position)
        (second.evaluate position) := by
  simp [conjoin, TransitionProgram.conjoin, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_disjoin (first second : Program) (position : Nat) :
    (disjoin first second).evaluate position =
      TransitionProgram.disjoin (first.evaluate position)
        (second.evaluate position) := by
  simp [disjoin, TransitionProgram.disjoin, Program.evaluate,
    Instruction.evaluate]

@[simp]
theorem evaluate_all (inputs : List Program) (position : Nat) :
    (all inputs).evaluate position =
      TransitionProgram.all (inputs.map (Program.evaluate position)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs induction =>
      simp [all, TransitionProgram.all, induction]

@[simp]
theorem evaluate_any (inputs : List Program) (position : Nat) :
    (any inputs).evaluate position =
      TransitionProgram.any (inputs.map (Program.evaluate position)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs induction =>
      simp [any, TransitionProgram.any, induction]

@[simp]
theorem evaluate_equal (first second : Program) (position : Nat) :
    (equal first second).evaluate position =
      TransitionProgram.equal (first.evaluate position)
        (second.evaluate position) := by
  simp [equal, TransitionProgram.equal]

@[simp]
theorem evaluate_vectorsEqual (first second : List Atom) (position : Nat) :
    (vectorsEqual first second).evaluate position =
      TransitionProgram.vectorsEqual (first.map (Atom.evaluate position))
        (second.map (Atom.evaluate position)) := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons first firsts induction =>
      cases second with
      | nil => rfl
      | cons second seconds =>
          simp [vectorsEqual, TransitionProgram.vectorsEqual, induction]

@[simp]
theorem evaluate_exactlyOne (inputs : List Program) (position : Nat) :
    (exactlyOne inputs).evaluate position =
      TransitionProgram.exactlyOne
        (inputs.map (Program.evaluate position)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs induction =>
      simp [exactlyOne, TransitionProgram.exactlyOne, induction,
        List.map_map, Function.comp_def]

@[simp]
theorem evaluate_currentExactlyOne (atoms : List Atom) (position : Nat) :
    (currentExactlyOne atoms).evaluate position =
      TransitionProgram.currentExactlyOne
        (atoms.map (Atom.evaluate position)) := by
  simp [currentExactlyOne, TransitionProgram.currentExactlyOne,
    List.map_map, Function.comp_def]

@[simp]
theorem evaluate_binarySuccessor (currentAtoms nextAtoms : List Atom)
    (position : Nat) :
    (binarySuccessor currentAtoms nextAtoms).evaluate position =
      TransitionProgram.binarySuccessor
        (currentAtoms.map (Atom.evaluate position))
        (nextAtoms.map (Atom.evaluate position)) := by
  induction currentAtoms generalizing nextAtoms with
  | nil => cases nextAtoms <;> rfl
  | cons currentAtom currentAtoms induction =>
      cases nextAtoms with
      | nil => rfl
      | cons nextAtom nextAtoms =>
          simp [binarySuccessor, TransitionProgram.binarySuccessor,
            induction]

end AffineProgramTemplates
end PeriodicCNF
end LeanTrominoes
