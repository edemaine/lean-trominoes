/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseArityData

/-! # Clause-arity scan agrees with structural Tseitin compilation -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace UnaryProgramClauseArity

theorem compileTransitionExpr_clauseLengths
    (expression : TransitionExpr) (fresh : Nat) :
    (compileTransitionExpr expression fresh).clauses.map List.length =
      (expression.program.flatMap instructionArities).map Arity.value := by
  induction expression generalizing fresh with
  | constant value =>
      cases value <;>
        simp [compileTransitionExpr, TransitionExpr.program,
          constantClauses, instructionArities, Arity.value]
  | wire input =>
      simp [compileTransitionExpr, TransitionExpr.program,
        equalityClauses, instructionArities, Arity.value]
  | not input induction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        notClauses, instructionArities, Arity.value, induction]
  | and first second firstInduction secondInduction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        andClauses, instructionArities, Arity.value,
        firstInduction, secondInduction]
  | or first second firstInduction secondInduction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        orClauses, instructionArities, Arity.value,
        firstInduction, secondInduction]

/-- Scanning the unary request and interpreting each finite arity tag gives
the clause-length list of the exact forced transition formula, including its
final root clause. -/
theorem requestScan_values_eq_clauseLengths
    (expression : TransitionExpr) (fresh : Nat) :
    (requestScan
        (UnaryProgramTokens.requestSource fresh expression.program)).map
          Arity.value =
      (requireTransitionExpr expression fresh).clauses.map List.length := by
  rw [requestScan_requestSource]
  unfold requireTransitionExpr
  rw [List.map_append, List.map_append,
    compileTransitionExpr_clauseLengths]
  simp [constantClauses, Arity.value]

end UnaryProgramClauseArity
end PeriodicCNF
end LeanTrominoes
