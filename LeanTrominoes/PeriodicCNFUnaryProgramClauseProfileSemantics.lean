/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Clause-profile scan agrees with structural Tseitin compilation -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace UnaryProgramClauseProfile

/-- Extract the route-relevant finite profile of a semantic literal. -/
def LiteralProfile.ofLiteral (literal : PeriodicLiteral Nat) :
    LiteralProfile where
  nextSlice := decide (literal.offset = (1, 0))
  value := literal.value

theorem compileTransitionExpr_clauseProfiles
    (expression : TransitionExpr) (fresh : Nat) :
    (compileTransitionExpr expression fresh).clauses.map
        (List.map LiteralProfile.ofLiteral) =
      (expression.program.flatMap instructionProfiles).map
        ClauseProfile.literals := by
  induction expression generalizing fresh with
  | constant value =>
      cases value <;>
        simp [compileTransitionExpr, TransitionExpr.program,
          constantClauses, instructionProfiles, ClauseProfile.literals,
          LiteralProfile.ofLiteral, current, TransitionWire.literal,
          gateOutput]
  | wire wire =>
      rcases wire with ⟨slice, atom⟩
      cases slice <;>
        simp [compileTransitionExpr, TransitionExpr.program,
          equalityClauses, instructionProfiles, ClauseProfile.literals,
          LiteralProfile.ofLiteral, current, input,
          ProgramTokens.sliceBool, TransitionWire.literal, gateOutput]
  | not expression induction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        notClauses, instructionProfiles, ClauseProfile.literals,
        LiteralProfile.ofLiteral, current, TransitionWire.literal,
        gateOutput, induction]
  | and first second firstInduction secondInduction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        andClauses, instructionProfiles, ClauseProfile.literals,
        LiteralProfile.ofLiteral, current, TransitionWire.literal,
        gateOutput, firstInduction, secondInduction]
  | or first second firstInduction secondInduction =>
      simp [compileTransitionExpr, TransitionExpr.program,
        orClauses, instructionProfiles, ClauseProfile.literals,
        LiteralProfile.ofLiteral, current, TransitionWire.literal,
        gateOutput, firstInduction, secondInduction]

/-- The complete finite scan equals the polarity-and-slice profile of every
clause in the exact forced transition formula. -/
theorem requestScan_literals_eq_clauseProfiles
    (expression : TransitionExpr) (fresh : Nat) :
    (requestScan
        (UnaryProgramTokens.requestSource fresh expression.program)).map
          ClauseProfile.literals =
      (requireTransitionExpr expression fresh).clauses.map
        (List.map LiteralProfile.ofLiteral) := by
  rw [requestScan_requestSource]
  unfold requireTransitionExpr
  rw [List.map_append, List.map_append,
    compileTransitionExpr_clauseProfiles]
  simp [constantClauses, ClauseProfile.literals,
    LiteralProfile.ofLiteral, current, TransitionWire.literal,
    gateOutput]

end UnaryProgramClauseProfile
end PeriodicCNF
end LeanTrominoes
