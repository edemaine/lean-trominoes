/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprFields

/-!
# Postorder programs for transition-expression compilation

The direct field compiler is structurally recursive on a `TransitionExpr`.
For a finite machine, a flat postorder instruction stream is a better
interface: one left-to-right pass maintains the next fresh atom and a stack of
completed roots, while emitting the same fixed gate field blocks.

This file defines that instruction stream, proves its interpreter exactly
matches `compileTransitionFields`, and gives a compact flat natural-field
encoding with at most three fields per expression node.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- One postorder instruction of the structural Tseitin compiler. -/
inductive TransitionInstruction
  | constant (value : Bool)
  | wire (input : TransitionWire)
  | negate
  | conjoin
  | disjoin
  deriving DecidableEq, Repr

namespace TransitionInstruction

/-- Number of clauses emitted by one instruction. -/
def clauseCount : TransitionInstruction → Nat
  | .constant _ => 1
  | .wire _ => 2
  | .negate => 2
  | .conjoin => 3
  | .disjoin => 3

/-- Compact natural fields for one instruction.  Tags `0` through `4`
distinguish the constructors; constants and wires carry their finite payload. -/
def fields : TransitionInstruction → List Nat
  | .constant value => [0, if value then 1 else 0]
  | .wire input =>
      [1, match input.slice with
          | .current => 0
          | .next => 1,
        input.atom]
  | .negate => [2]
  | .conjoin => [3]
  | .disjoin => [4]

theorem fields_length_le_three (instruction : TransitionInstruction) :
    instruction.fields.length ≤ 3 := by
  cases instruction with
  | constant value => simp [fields]
  | wire input =>
      rcases input with ⟨slice, atom⟩
      cases slice <;> simp [fields]
  | negate => simp [fields]
  | conjoin => simp [fields]
  | disjoin => simp [fields]

end TransitionInstruction

namespace TransitionExpr

/-- Postorder traversal of an expression tree. -/
def program : TransitionExpr → List TransitionInstruction
  | .constant value => [.constant value]
  | .wire input => [.wire input]
  | .not input => input.program ++ [.negate]
  | .and first second => first.program ++ second.program ++ [.conjoin]
  | .or first second => first.program ++ second.program ++ [.disjoin]

@[simp]
theorem program_length (expression : TransitionExpr) :
    expression.program.length = expression.gateCount := by
  induction expression with
  | constant value => rfl
  | wire input => rfl
  | not input induction =>
      simp [program, gateCount, induction]
  | and first second firstIH secondIH =>
      simp [program, gateCount, firstIH, secondIH]
      omega
  | or first second firstIH secondIH =>
      simp [program, gateCount, firstIH, secondIH]
      omega

@[simp]
theorem program_clauseCount (expression : TransitionExpr) :
    (expression.program.map TransitionInstruction.clauseCount).sum =
      expression.clauseCount := by
  induction expression with
  | constant value => rfl
  | wire input => rfl
  | not input induction =>
      simp [program, clauseCount, TransitionInstruction.clauseCount,
        induction]
  | and first second firstIH secondIH =>
      simp [program, clauseCount, TransitionInstruction.clauseCount,
        firstIH, secondIH]
      omega
  | or first second firstIH secondIH =>
      simp [program, clauseCount, TransitionInstruction.clauseCount,
        firstIH, secondIH]
      omega

end TransitionExpr

/-- State of the postorder field compiler.  Completed roots are stored newest
first, matching a physical stack. -/
structure TransitionProgramState where
  nextFresh : Nat
  roots : List Nat
  fields : List Nat
  deriving DecidableEq, Repr

/-- Execute one postorder instruction.  Malformed unary or binary stack
operations are total no-ops; generated programs never take those branches. -/
def executeTransitionInstruction
    (state : TransitionProgramState) :
    TransitionInstruction → TransitionProgramState
  | .constant value =>
      ⟨state.nextFresh + 1, state.nextFresh :: state.roots,
        state.fields ++ constantGateFields state.nextFresh value⟩
  | .wire input =>
      ⟨state.nextFresh + 1, state.nextFresh :: state.roots,
        state.fields ++ equalityGateFields state.nextFresh input⟩
  | .negate =>
      match state.roots with
      | input :: rest =>
          ⟨state.nextFresh + 1, state.nextFresh :: rest,
            state.fields ++
              notGateFields state.nextFresh (gateOutput input)⟩
      | [] => state
  | .conjoin =>
      match state.roots with
      | second :: first :: rest =>
          ⟨state.nextFresh + 1, state.nextFresh :: rest,
            state.fields ++ andGateFields state.nextFresh
              (gateOutput first) (gateOutput second)⟩
      | _ => state
  | .disjoin =>
      match state.roots with
      | second :: first :: rest =>
          ⟨state.nextFresh + 1, state.nextFresh :: rest,
            state.fields ++ orGateFields state.nextFresh
              (gateOutput first) (gateOutput second)⟩
      | _ => state

/-- Execute a flat instruction stream from left to right. -/
def executeTransitionProgram :
    List TransitionInstruction →
      TransitionProgramState → TransitionProgramState
  | [], state => state
  | instruction :: instructions, state =>
      executeTransitionProgram instructions
        (executeTransitionInstruction state instruction)

@[simp]
theorem executeTransitionProgram_nil (state : TransitionProgramState) :
    executeTransitionProgram [] state = state :=
  rfl

theorem executeTransitionProgram_append
    (first second : List TransitionInstruction)
    (state : TransitionProgramState) :
    executeTransitionProgram (first ++ second) state =
      executeTransitionProgram second
        (executeTransitionProgram first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction instructions induction =>
      simp only [List.cons_append, executeTransitionProgram]
      exact induction _

/-- Executing the postorder program of one expression pushes precisely its
compiled root, advances to the same fresh boundary, and appends exactly its
direct clause fields. -/
theorem executeTransitionProgram_expression
    (expression : TransitionExpr) (fresh : Nat)
    (roots : List Nat) (initialFields : List Nat) :
    executeTransitionProgram expression.program
        ⟨fresh, roots, initialFields⟩ =
      ⟨(compileTransitionFields expression fresh).nextFresh,
        (compileTransitionFields expression fresh).root :: roots,
        initialFields ++ (compileTransitionFields expression fresh).fields⟩ := by
  induction expression generalizing fresh roots initialFields with
  | constant value =>
      simp [TransitionExpr.program, executeTransitionProgram,
        executeTransitionInstruction, compileTransitionFields]
  | wire input =>
      simp [TransitionExpr.program, executeTransitionProgram,
        executeTransitionInstruction, compileTransitionFields]
  | not input induction =>
      rw [TransitionExpr.program, executeTransitionProgram_append,
        induction]
      simp [executeTransitionProgram, executeTransitionInstruction,
        compileTransitionFields, List.append_assoc]
  | and first second firstIH secondIH =>
      rw [TransitionExpr.program, executeTransitionProgram_append,
        executeTransitionProgram_append, firstIH, secondIH]
      simp [executeTransitionProgram, executeTransitionInstruction,
        compileTransitionFields, List.append_assoc]
  | or first second firstIH secondIH =>
      rw [TransitionExpr.program, executeTransitionProgram_append,
        executeTransitionProgram_append, firstIH, secondIH]
      simp [executeTransitionProgram, executeTransitionInstruction,
        compileTransitionFields, List.append_assoc]

/-- Natural-field stream of a postorder instruction program. -/
def transitionProgramFields (program : List TransitionInstruction) : List Nat :=
  program.flatMap TransitionInstruction.fields

theorem transitionProgramFields_length_le
    (program : List TransitionInstruction) :
    (transitionProgramFields program).length ≤ 3 * program.length := by
  induction program with
  | nil => simp [transitionProgramFields]
  | cons instruction program induction =>
      rw [show transitionProgramFields (instruction :: program) =
          instruction.fields ++ transitionProgramFields program by rfl]
      simp only [List.length_append, List.length_cons]
      have instructionBound := instruction.fields_length_le_three
      omega

theorem expression_program_fields_length_le
    (expression : TransitionExpr) :
    (transitionProgramFields expression.program).length ≤
      3 * expression.gateCount := by
  simpa using transitionProgramFields_length_le expression.program

/-- Final clause fields obtained by interpreting the expression's postorder
program and forcing its unique root. -/
def requireTransitionProgramFields
    (expression : TransitionExpr) (fresh : Nat) : List Nat :=
  let state := executeTransitionProgram expression.program
    ⟨fresh, [], []⟩
  (expression.clauseCount + 1) ::
    state.fields ++ constantGateFields state.roots.head! true

/-- The postorder interpreter is extensionally identical to the direct
structural field compiler. -/
theorem requireTransitionProgramFields_eq
    (expression : TransitionExpr) (fresh : Nat) :
    requireTransitionProgramFields expression fresh =
      requireTransitionExprFields expression fresh := by
  rw [requireTransitionProgramFields,
    executeTransitionProgram_expression]
  simp [requireTransitionExprFields]

end PeriodicCNF
end LeanTrominoes
