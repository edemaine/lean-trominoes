/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFTransitionProgramVectors
import LeanTrominoes.PeriodicCNFTransitionExprFormula

/-! # Exact literal counts for transition programs -/

namespace LeanTrominoes
namespace PeriodicCNF

namespace TransitionInstruction

/-- Number of literal occurrences in the Tseitin clauses emitted by one
postorder instruction. -/
def literalCount : TransitionInstruction → Nat
  | .constant _ => 1
  | .wire _ => 4
  | .negate => 4
  | .conjoin => 7
  | .disjoin => 7

end TransitionInstruction

namespace TransitionProgram

/-- Literal occurrences accumulated directly from a postorder program. -/
def literalCount (program : Program) : Nat :=
  (program.map TransitionInstruction.literalCount).sum

end TransitionProgram

namespace TransitionExpr

/-- Structural literal count of the Tseitin clauses before the final forced
root clause. -/
def literalCount : TransitionExpr → Nat
  | .constant _ => 1
  | .wire _ => 4
  | .not input => input.literalCount + 4
  | .and first second => first.literalCount + second.literalCount + 7
  | .or first second => first.literalCount + second.literalCount + 7

@[simp] theorem program_literalCount (expression : TransitionExpr) :
    TransitionProgram.literalCount expression.program =
      expression.literalCount := by
  induction expression with
  | constant value => rfl
  | wire input => rfl
  | not input induction =>
      unfold TransitionProgram.literalCount at induction
      unfold TransitionProgram.literalCount
      simp only [program, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton,
        TransitionInstruction.literalCount, literalCount]
      rw [induction]
  | and first second firstIH secondIH =>
      unfold TransitionProgram.literalCount at firstIH secondIH
      unfold TransitionProgram.literalCount
      simp only [program, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton,
        TransitionInstruction.literalCount, literalCount]
      rw [firstIH, secondIH]
  | or first second firstIH secondIH =>
      unfold TransitionProgram.literalCount at firstIH secondIH
      unfold TransitionProgram.literalCount
      simp only [program, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton,
        TransitionInstruction.literalCount, literalCount]
      rw [firstIH, secondIH]

end TransitionExpr

/-- The structural compiler's stored clauses have exactly the program's
literal weight. -/
theorem compileTransitionExpr_presentationLiteralCount
    (expression : TransitionExpr) (fresh : Nat) :
    PeriodicCNF.presentationLiteralCount
        ⟨(compileTransitionExpr expression fresh).clauses⟩ =
      expression.literalCount := by
  induction expression generalizing fresh with
  | constant value =>
      simp [compileTransitionExpr, TransitionExpr.literalCount,
        PeriodicCNF.presentationLiteralCount, constantClauses]
  | wire input =>
      simp [compileTransitionExpr, TransitionExpr.literalCount,
        PeriodicCNF.presentationLiteralCount, equalityClauses]
  | not input induction =>
      simp only [PeriodicCNF.presentationLiteralCount,
        List.length_flatten] at induction ⊢
      simp only [compileTransitionExpr, List.map_append, List.sum_append,
        notClauses, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil, List.sum_cons, List.sum_nil,
        TransitionExpr.literalCount]
      rw [induction]
      omega
  | and first second firstIH secondIH =>
      simp only [PeriodicCNF.presentationLiteralCount,
        List.length_flatten] at firstIH secondIH ⊢
      simp only [compileTransitionExpr, List.map_append, List.sum_append,
        andClauses, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil, List.sum_cons, List.sum_nil,
        TransitionExpr.literalCount]
      rw [firstIH, secondIH]
      omega
  | or first second firstIH secondIH =>
      simp only [PeriodicCNF.presentationLiteralCount,
        List.length_flatten] at firstIH secondIH ⊢
      simp only [compileTransitionExpr, List.map_append, List.sum_append,
        orClauses, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil, List.sum_cons, List.sum_nil,
        TransitionExpr.literalCount]
      rw [firstIH, secondIH]
      omega

/-- Forcing the compiled root contributes one final literal occurrence. -/
@[simp] theorem requireTransitionExpr_presentationLiteralCount
    (expression : TransitionExpr) (fresh : Nat) :
    PeriodicCNF.presentationLiteralCount
        (requireTransitionExpr expression fresh) =
      TransitionProgram.literalCount expression.program + 1 := by
  rw [TransitionExpr.program_literalCount]
  unfold requireTransitionExpr PeriodicCNF.presentationLiteralCount
  rw [List.flatten_append, List.length_append]
  rw [show (List.flatten
      (compileTransitionExpr expression fresh).clauses).length =
        expression.literalCount by
      exact compileTransitionExpr_presentationLiteralCount expression fresh]
  simp [constantClauses]

end PeriodicCNF
end LeanTrominoes
