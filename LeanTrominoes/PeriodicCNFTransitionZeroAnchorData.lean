/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExpr
import LeanTrominoes.PeriodicCNFZeroAnchorData

/-! # Zero anchors of transition-gate clauses -/

namespace LeanTrominoes
namespace PeriodicCNF

@[simp] theorem constantClauses_zeroAnchored
    (output : Nat) (value : Bool) :
    ClausesZeroAnchored (constantClauses output value) := by
  simp [ClausesZeroAnchored, constantClauses, clauseAnchor,
    gateOutput, TransitionWire.literal]

@[simp] theorem equalityClauses_zeroAnchored
    (output : Nat) (input : TransitionWire) :
    ClausesZeroAnchored (equalityClauses output input) := by
  simp [ClausesZeroAnchored, equalityClauses, clauseAnchor,
    gateOutput, TransitionWire.literal]

@[simp] theorem notClauses_zeroAnchored
    (output : Nat) (input : TransitionWire) :
    ClausesZeroAnchored (notClauses output input) := by
  simp [ClausesZeroAnchored, notClauses, clauseAnchor,
    gateOutput, TransitionWire.literal]

@[simp] theorem andClauses_zeroAnchored
    (output : Nat) (first second : TransitionWire) :
    ClausesZeroAnchored (andClauses output first second) := by
  simp [ClausesZeroAnchored, andClauses, clauseAnchor,
    gateOutput, TransitionWire.literal]

@[simp] theorem orClauses_zeroAnchored
    (output : Nat) (first second : TransitionWire) :
    ClausesZeroAnchored (orClauses output first second) := by
  simp [ClausesZeroAnchored, orClauses, clauseAnchor,
    gateOutput, TransitionWire.literal]

end PeriodicCNF
end LeanTrominoes
