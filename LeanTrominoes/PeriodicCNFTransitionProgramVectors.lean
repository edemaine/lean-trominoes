/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionProgram

/-!
# Compositional postorder programs for Boolean-vector expressions

The bounded-machine request printer must stream a postorder instruction word
without first constructing its exponentially large semantic syntax tree.
This file mirrors the reusable `TransitionExpr` combinators directly at the
instruction-list level and proves that each mirror is exactly the ordinary
postorder traversal.

Later printer phases can therefore work only with finite instruction blocks,
list folds, and numeric atom streams while reusing the semantic theorems for
the original expression combinators.
-/

namespace LeanTrominoes
namespace PeriodicCNF

namespace TransitionProgram

abbrev Program := List TransitionInstruction

def constant (value : Bool) : Program :=
  [.constant value]

def wire (slice : TransitionSlice) (atom : Nat) : Program :=
  [.wire ⟨slice, atom⟩]

def current (atom : Nat) : Program :=
  wire .current atom

def next (atom : Nat) : Program :=
  wire .next atom

def negate (input : Program) : Program :=
  input ++ [.negate]

def conjoin (first second : Program) : Program :=
  first ++ second ++ [.conjoin]

def disjoin (first second : Program) : Program :=
  first ++ second ++ [.disjoin]

/-- Postorder program of a finite conjunction. -/
def all : List Program → Program
  | [] => constant true
  | input :: inputs => conjoin input (all inputs)

/-- Postorder program of a finite disjunction. -/
def any : List Program → Program
  | [] => constant false
  | input :: inputs => disjoin input (any inputs)

/-- Postorder program of Boolean equality. -/
def equal (first second : Program) : Program :=
  disjoin (conjoin first second)
    (conjoin (negate first) (negate second))

/-- Postorder program of equality between current and next atom vectors. -/
def vectorsEqual : List Nat → List Nat → Program
  | [], [] => constant true
  | first :: firsts, second :: seconds =>
      conjoin (equal (current first) (next second))
        (vectorsEqual firsts seconds)
  | _, _ => constant false

/-- Postorder program asserting exactly one Boolean subprogram is true. -/
def exactlyOne : List Program → Program
  | [] => constant false
  | input :: inputs =>
      disjoin
        (conjoin input (all (inputs.map negate)))
        (conjoin (negate input) (exactlyOne inputs))

/-- Postorder program asserting exactly one current atom is true. -/
def currentExactlyOne (atoms : List Nat) : Program :=
  exactlyOne (atoms.map current)

/-- Postorder program for little-endian, no-overflow binary succession. -/
def binarySuccessor : List Nat → List Nat → Program
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

/-- Clause count accumulated directly from a postorder instruction word. -/
def clauseCount (program : Program) : Nat :=
  (program.map TransitionInstruction.clauseCount).sum

end TransitionProgram

namespace TransitionExpr

@[simp]
theorem program_constant (value : Bool) :
    (TransitionExpr.constant value).program =
      TransitionProgram.constant value :=
  rfl

@[simp]
theorem program_wire (input : TransitionWire) :
    (TransitionExpr.wire input).program =
      TransitionProgram.wire input.slice input.atom :=
  rfl

@[simp]
theorem program_current (atom : Nat) :
    (current atom).program = TransitionProgram.current atom :=
  rfl

@[simp]
theorem program_next (atom : Nat) :
    (next atom).program = TransitionProgram.next atom :=
  rfl

@[simp]
theorem program_not (input : TransitionExpr) :
    (TransitionExpr.not input).program =
      TransitionProgram.negate input.program :=
  rfl

@[simp]
theorem program_and (first second : TransitionExpr) :
    (TransitionExpr.and first second).program =
      TransitionProgram.conjoin first.program second.program :=
  rfl

@[simp]
theorem program_or (first second : TransitionExpr) :
    (TransitionExpr.or first second).program =
      TransitionProgram.disjoin first.program second.program :=
  rfl

@[simp]
theorem program_all (expressions : List TransitionExpr) :
    (all expressions).program =
      TransitionProgram.all (expressions.map TransitionExpr.program) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions induction =>
      simp [all, TransitionProgram.all, induction]

@[simp]
theorem program_any (expressions : List TransitionExpr) :
    (any expressions).program =
      TransitionProgram.any (expressions.map TransitionExpr.program) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions induction =>
      simp [any, TransitionProgram.any, induction]

@[simp]
theorem program_equal (first second : TransitionExpr) :
    (equal first second).program =
      TransitionProgram.equal first.program second.program := by
  rfl

@[simp]
theorem program_vectorsEqual (first second : List Nat) :
    (vectorsEqual first second).program =
      TransitionProgram.vectorsEqual first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons first firsts induction =>
      cases second with
      | nil => rfl
      | cons second seconds =>
          simp [vectorsEqual, TransitionProgram.vectorsEqual, induction]

@[simp]
theorem program_exactlyOne (expressions : List TransitionExpr) :
    (exactlyOne expressions).program =
      TransitionProgram.exactlyOne
        (expressions.map TransitionExpr.program) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions induction =>
      simp [exactlyOne, TransitionProgram.exactlyOne, induction,
        List.map_map, Function.comp_def]

@[simp]
theorem program_currentExactlyOne (atoms : List Nat) :
    (currentExactlyOne atoms).program =
      TransitionProgram.currentExactlyOne atoms := by
  simp [currentExactlyOne, TransitionProgram.currentExactlyOne,
    List.map_map, Function.comp_def]

@[simp]
theorem program_binarySuccessor (currentAtoms nextAtoms : List Nat) :
    (binarySuccessor currentAtoms nextAtoms).program =
      TransitionProgram.binarySuccessor currentAtoms nextAtoms := by
  induction currentAtoms generalizing nextAtoms with
  | nil => cases nextAtoms <;> rfl
  | cons currentAtom currentAtoms induction =>
      cases nextAtoms with
      | nil => rfl
      | cons nextAtom nextAtoms =>
          simp [binarySuccessor, TransitionProgram.binarySuccessor,
            induction]

@[simp]
theorem TransitionProgram.clauseCount_program
    (expression : TransitionExpr) :
    TransitionProgram.clauseCount expression.program =
      expression.clauseCount := by
  exact TransitionExpr.program_clauseCount expression

end TransitionExpr

end PeriodicCNF
end LeanTrominoes
