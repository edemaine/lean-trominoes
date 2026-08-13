import LeanTrominoes.PeriodicCNFTransitionProgram

/-!
# Native encoding of transition compiler programs

This file fixes the exact evaluator boundary for structural Tseitin
compilation.  A compiler request contains the final clause-count header, the
first fresh atom, and a compact postorder instruction stream.  Its total
field-level evaluator decodes the stream, runs the verified stack interpreter,
and emits the complete flat formula fields.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Total decoder for compact postorder instruction fields.  Invalid or
truncated suffixes stop the program; generated streams round trip exactly. -/
def decodeTransitionProgram : List Nat → List TransitionInstruction
  | 0 :: value :: rest =>
      .constant (value != 0) :: decodeTransitionProgram rest
  | 1 :: slice :: atom :: rest =>
      .wire ⟨if slice = 0 then .current else .next, atom⟩ ::
        decodeTransitionProgram rest
  | 2 :: rest => .negate :: decodeTransitionProgram rest
  | 3 :: rest => .conjoin :: decodeTransitionProgram rest
  | 4 :: rest => .disjoin :: decodeTransitionProgram rest
  | _ => []

@[simp]
theorem decodeTransitionProgram_fields
    (program : List TransitionInstruction) :
    decodeTransitionProgram (transitionProgramFields program) = program := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show transitionProgramFields (instruction :: program) =
          instruction.fields ++ transitionProgramFields program by rfl]
      cases instruction with
      | constant value =>
          cases value <;>
            simp [TransitionInstruction.fields,
              decodeTransitionProgram, induction]
      | wire input =>
          rcases input with ⟨slice, atom⟩
          cases slice <;>
            simp [TransitionInstruction.fields,
              decodeTransitionProgram, induction]
      | negate =>
          simp [TransitionInstruction.fields,
            decodeTransitionProgram, induction]
      | conjoin =>
          simp [TransitionInstruction.fields,
            decodeTransitionProgram, induction]
      | disjoin =>
          simp [TransitionInstruction.fields,
            decodeTransitionProgram, induction]

/-- Native request fields for compiling one expression. -/
def transitionCompilerInputFields
    (expression : TransitionExpr) (fresh : Nat) : List Nat :=
  (expression.clauseCount + 1) :: fresh ::
    transitionProgramFields expression.program

/-- Total field-level evaluator for one compact transition compiler request. -/
def transitionCompilerEvaluatorFields : List Nat → List Nat
  | clauseCount :: fresh :: programFields =>
      let state := executeTransitionProgram
        (decodeTransitionProgram programFields) ⟨fresh, [], []⟩
      clauseCount ::
        state.fields ++ constantGateFields state.roots.head! true
  | _ => []

/-- The field-level evaluator compiles every generated request to the exact
verified flat formula stream. -/
@[simp]
theorem transitionCompilerEvaluatorFields_input
    (expression : TransitionExpr) (fresh : Nat) :
    transitionCompilerEvaluatorFields
        (transitionCompilerInputFields expression fresh) =
      requireTransitionExprFields expression fresh := by
  unfold transitionCompilerInputFields
  simp only [transitionCompilerEvaluatorFields,
    decodeTransitionProgram_fields]
  exact requireTransitionProgramFields_eq expression fresh

@[simp]
theorem transitionCompilerInputFields_length
    (expression : TransitionExpr) (fresh : Nat) :
    (transitionCompilerInputFields expression fresh).length =
      (transitionProgramFields expression.program).length + 2 := by
  simp [transitionCompilerInputFields]

theorem transitionCompilerInputFields_length_le
    (expression : TransitionExpr) (fresh : Nat) :
    (transitionCompilerInputFields expression fresh).length ≤
      3 * expression.gateCount + 2 := by
  rw [transitionCompilerInputFields_length]
  exact Nat.add_le_add_right
    (expression_program_fields_length_le expression) 2

end PeriodicCNF
end LeanTrominoes
