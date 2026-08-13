/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionGates

/-!
# Compiling transition expressions to periodic CNF

This file assembles the constant-size gate encodings into a structural
Tseitin compiler.  Every expression node receives one fresh current-slice
atom, so both the generated atom range and clause count are linear in the
expression tree.
-/

namespace LeanTrominoes

namespace PeriodicCNF

/-- Boolean expressions over current- and next-slice transition wires. -/
inductive TransitionExpr
  | constant (value : Bool)
  | wire (input : TransitionWire)
  | not (input : TransitionExpr)
  | and (first second : TransitionExpr)
  | or (first second : TransitionExpr)
  deriving DecidableEq, Repr

namespace TransitionExpr

/-- Direct evaluation of a transition expression. -/
def eval : TransitionExpr → (Nat → Bool) → (Nat → Bool) → Bool
  | .constant value, _, _ => value
  | .wire input, current, next => input.value current next
  | .not input, current, next => !(input.eval current next)
  | .and first second, current, next =>
      first.eval current next && second.eval current next
  | .or first second, current, next =>
      first.eval current next || second.eval current next

/-- Number of Tseitin output atoms allocated by an expression. -/
def gateCount : TransitionExpr → Nat
  | .constant _ => 1
  | .wire _ => 1
  | .not input => input.gateCount + 1
  | .and first second => first.gateCount + second.gateCount + 1
  | .or first second => first.gateCount + second.gateCount + 1

/-- Exact number of clauses emitted by the structural compiler. -/
def clauseCount : TransitionExpr → Nat
  | .constant _ => 1
  | .wire _ => 2
  | .not input => input.clauseCount + 2
  | .and first second => first.clauseCount + second.clauseCount + 3
  | .or first second => first.clauseCount + second.clauseCount + 3

/-- All source atoms mentioned by an expression lie below a bound. -/
def AtomsBelow : TransitionExpr → Nat → Prop
  | .constant _, _ => True
  | .wire input, bound => input.atom < bound
  | .not input, bound => input.AtomsBelow bound
  | .and first second, bound =>
      first.AtomsBelow bound ∧ second.AtomsBelow bound
  | .or first second, bound =>
      first.AtomsBelow bound ∧ second.AtomsBelow bound

end TransitionExpr

/-- Output of compiling one transition expression. -/
structure CompiledTransitionExpr where
  nextFresh : Nat
  root : Nat
  clauses : List (PeriodicClause Nat)
  deriving DecidableEq, Repr

/-- Structural Tseitin compilation.  Each recursive result is followed by one
new gate whose output becomes the root of the enclosing expression. -/
def compileTransitionExpr : TransitionExpr → Nat → CompiledTransitionExpr
  | .constant value, fresh =>
      ⟨fresh + 1, fresh, constantClauses fresh value⟩
  | .wire input, fresh =>
      ⟨fresh + 1, fresh, equalityClauses fresh input⟩
  | .not input, fresh =>
      let compiled := compileTransitionExpr input fresh
      ⟨compiled.nextFresh + 1, compiled.nextFresh,
        compiled.clauses ++
          notClauses compiled.nextFresh (gateOutput compiled.root)⟩
  | .and first second, fresh =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
        firstCompiled.clauses ++ secondCompiled.clauses ++
          andClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)⟩
  | .or first second, fresh =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
        firstCompiled.clauses ++ secondCompiled.clauses ++
          orClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)⟩

@[simp]
theorem compileTransitionExpr_nextFresh (expression : TransitionExpr)
    (fresh : Nat) :
    (compileTransitionExpr expression fresh).nextFresh =
      fresh + expression.gateCount := by
  induction expression generalizing fresh with
  | constant value => simp [compileTransitionExpr, TransitionExpr.gateCount]
  | wire input => simp [compileTransitionExpr, TransitionExpr.gateCount]
  | not input ih =>
      simp [compileTransitionExpr, TransitionExpr.gateCount, ih]
      omega
  | and first second firstIH secondIH =>
      simp [compileTransitionExpr, TransitionExpr.gateCount,
        firstIH, secondIH]
      omega
  | or first second firstIH secondIH =>
      simp [compileTransitionExpr, TransitionExpr.gateCount,
        firstIH, secondIH]
      omega

theorem compileTransitionExpr_fresh_le_root (expression : TransitionExpr)
    (fresh : Nat) :
    fresh ≤ (compileTransitionExpr expression fresh).root := by
  cases expression <;>
    simp [compileTransitionExpr, compileTransitionExpr_nextFresh] <;>
    omega

theorem compileTransitionExpr_root_lt_nextFresh (expression : TransitionExpr)
    (fresh : Nat) :
    (compileTransitionExpr expression fresh).root <
      (compileTransitionExpr expression fresh).nextFresh := by
  cases expression <;> simp [compileTransitionExpr]

@[simp]
theorem compileTransitionExpr_clause_length (expression : TransitionExpr)
    (fresh : Nat) :
    (compileTransitionExpr expression fresh).clauses.length =
      expression.clauseCount := by
  induction expression generalizing fresh with
  | constant value =>
      simp [compileTransitionExpr, TransitionExpr.clauseCount,
        constantClauses]
  | wire input =>
      simp [compileTransitionExpr, TransitionExpr.clauseCount,
        equalityClauses]
  | not input ih =>
      simp [compileTransitionExpr, TransitionExpr.clauseCount,
        ih, notClauses]
  | and first second firstIH secondIH =>
      simp [compileTransitionExpr, TransitionExpr.clauseCount,
        firstIH, secondIH, andClauses]
      omega
  | or first second firstIH secondIH =>
      simp [compileTransitionExpr, TransitionExpr.clauseCount,
        firstIH, secondIH, orClauses]
      omega

private theorem forward_append
    {first second : List (PeriodicClause Nat)}
    (firstForward : (⟨first⟩ : PeriodicCNF Nat).IsForwardLocal)
    (secondForward : (⟨second⟩ : PeriodicCNF Nat).IsForwardLocal) :
    (⟨first ++ second⟩ : PeriodicCNF Nat).IsForwardLocal := by
  intro clause clauseMem literal literalMem
  rcases List.mem_append.mp clauseMem with inFirst | inSecond
  · exact firstForward clause inFirst literal literalMem
  · exact secondForward clause inSecond literal literalMem

/-- Structural compilation preserves the forward-local fragment. -/
theorem compileTransitionExpr_forward (expression : TransitionExpr)
    (fresh : Nat) :
    (⟨(compileTransitionExpr expression fresh).clauses⟩ :
      PeriodicCNF Nat).IsForwardLocal := by
  induction expression generalizing fresh with
  | constant value =>
      exact constantClauses_forward fresh value
  | wire input =>
      exact equalityClauses_forward fresh input
  | not input ih =>
      simp only [compileTransitionExpr]
      exact forward_append (ih fresh)
        (notClauses_forward
          (compileTransitionExpr input fresh).nextFresh
          (gateOutput (compileTransitionExpr input fresh).root))
  | and first second firstIH secondIH =>
      simp only [compileTransitionExpr]
      apply forward_append
      · exact forward_append (firstIH fresh)
          (secondIH (compileTransitionExpr first fresh).nextFresh)
      · exact andClauses_forward
          (compileTransitionExpr second
            (compileTransitionExpr first fresh).nextFresh).nextFresh
          (gateOutput (compileTransitionExpr first fresh).root)
          (gateOutput (compileTransitionExpr second
            (compileTransitionExpr first fresh).nextFresh).root)
  | or first second firstIH secondIH =>
      simp only [compileTransitionExpr]
      apply forward_append
      · exact forward_append (firstIH fresh)
          (secondIH (compileTransitionExpr first fresh).nextFresh)
      · exact orClauses_forward
          (compileTransitionExpr second
            (compileTransitionExpr first fresh).nextFresh).nextFresh
          (gateOutput (compileTransitionExpr first fresh).root)
          (gateOutput (compileTransitionExpr second
            (compileTransitionExpr first fresh).nextFresh).root)

end PeriodicCNF

end LeanTrominoes
