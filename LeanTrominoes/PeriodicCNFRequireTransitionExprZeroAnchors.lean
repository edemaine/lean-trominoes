/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprFormula
import LeanTrominoes.PeriodicCNFTransitionExprZeroAnchors

/-! # Zero anchors of required transition formulas -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Adding the unit clause that requires the compiled root preserves the
zero-anchor invariant. -/
theorem requireTransitionExpr_zeroAnchored
    (expression : TransitionExpr) (fresh : Nat) :
    (requireTransitionExpr expression fresh).IsZeroAnchored := by
  unfold IsZeroAnchored requireTransitionExpr
  apply clausesZeroAnchored_append
  · exact compileTransitionExpr_clauses_zeroAnchored expression fresh
  · simp

end PeriodicCNF
end LeanTrominoes
