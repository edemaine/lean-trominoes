/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionProgramVectors

/-!
# Flat schedule for binary-successor programs

The normalized no-overflow successor recursively compares every higher-bit
tail.  This file exposes its exact flat postorder schedule: each outer bit has
a rise test, all higher-bit equality operands, the equality/conjunction
ending, and a fall test; a final suffix closes the recursive disjunctions.
This is the semantic target for the triangular counter emitter.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace BinarySuccessorSchedule

abbrev Program := TransitionProgram.Program

/-- Equality of one current/next bit pair. -/
def equalityOperand (currentAtom nextAtom : Nat) : Program :=
  TransitionProgram.equal
    (TransitionProgram.current currentAtom)
    (TransitionProgram.next nextAtom)

/-- Concatenated equality operands, before their right-associated ending. -/
def equalityOperands : List Nat → List Nat → Program
  | currentAtom :: currentAtoms, nextAtom :: nextAtoms =>
      equalityOperand currentAtom nextAtom ++
        equalityOperands currentAtoms nextAtoms
  | _, _ => []

/-- Constant-true base and one conjunction instruction per equality operand. -/
def equalityEnding (count : Nat) : Program :=
  TransitionProgram.constant true ++
    List.replicate count .conjoin

/-- A complete vector equality is its operand stream followed by the fixed
right-associated ending. -/
theorem vectorsEqual_eq_schedule (currentAtoms nextAtoms : List Nat)
    (sameLength : currentAtoms.length = nextAtoms.length) :
    TransitionProgram.vectorsEqual currentAtoms nextAtoms =
      equalityOperands currentAtoms nextAtoms ++
        equalityEnding currentAtoms.length := by
  induction currentAtoms generalizing nextAtoms with
  | nil =>
      cases nextAtoms with
      | nil => rfl
      | cons nextAtom nextAtoms => simp at sameLength
  | cons currentAtom currentAtoms induction =>
      cases nextAtoms with
      | nil => simp at sameLength
      | cons nextAtom nextAtoms =>
          have tailLength : currentAtoms.length = nextAtoms.length := by
            simpa using sameLength
          rw [TransitionProgram.vectorsEqual]
          unfold TransitionProgram.conjoin
          rw [induction nextAtoms tailLength]
          simp [equalityOperand, equalityOperands, equalityEnding,
            List.replicate_succ', List.append_assoc]

/-- Low bit changes from zero to one. -/
def rise (currentAtom nextAtom : Nat) : Program :=
  TransitionProgram.conjoin
    (TransitionProgram.negate (TransitionProgram.current currentAtom))
    (TransitionProgram.next nextAtom)

/-- Low bit changes from one to zero and propagates the carry. -/
def fall (currentAtom nextAtom : Nat) : Program :=
  TransitionProgram.conjoin
    (TransitionProgram.current currentAtom)
    (TransitionProgram.negate (TransitionProgram.next nextAtom))

/-- Flat prefix emitted for one outer successor bit. -/
def frame (currentAtom nextAtom : Nat)
    (currentTail nextTail : List Nat) : Program :=
  rise currentAtom nextAtom ++
    equalityOperands currentTail nextTail ++
    equalityEnding currentTail.length ++
    [.conjoin] ++
    fall currentAtom nextAtom

/-- All outer frames, ordered from least to most significant bit. -/
def frames : List Nat → List Nat → Program
  | currentAtom :: currentAtoms, nextAtom :: nextAtoms =>
      frame currentAtom nextAtom currentAtoms nextAtoms ++
        frames currentAtoms nextAtoms
  | _, _ => []

/-- False no-overflow base followed by the conjunction/disjunction pair that
unwinds each recursive successor branch. -/
def ending : Nat → Program
  | 0 => TransitionProgram.constant false
  | count + 1 => ending count ++ [.conjoin, .disjoin]

/-- Exact flat schedule of the normalized no-overflow successor. -/
theorem binarySuccessor_eq_schedule (currentAtoms nextAtoms : List Nat)
    (sameLength : currentAtoms.length = nextAtoms.length) :
    TransitionProgram.binarySuccessor currentAtoms nextAtoms =
      frames currentAtoms nextAtoms ++ ending currentAtoms.length := by
  induction currentAtoms generalizing nextAtoms with
  | nil =>
      cases nextAtoms with
      | nil => rfl
      | cons nextAtom nextAtoms => simp at sameLength
  | cons currentAtom currentAtoms induction =>
      cases nextAtoms with
      | nil => simp at sameLength
      | cons nextAtom nextAtoms =>
          have tailLength : currentAtoms.length = nextAtoms.length := by
            simpa using sameLength
          rw [TransitionProgram.binarySuccessor]
          rw [induction nextAtoms tailLength]
          rw [vectorsEqual_eq_schedule currentAtoms nextAtoms tailLength]
          simp [TransitionProgram.disjoin, TransitionProgram.conjoin,
            frame, frames, rise, fall, ending, equalityEnding,
            List.append_assoc]

end BinarySuccessorSchedule
end PeriodicCNF
end LeanTrominoes
