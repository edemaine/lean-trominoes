/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprFormula
import LeanTrominoes.PeriodicCNFFlatEncoding

/-!
# Direct native fields for compiled transition expressions

The semantic Tseitin compiler first constructs nested clauses and the flat
encoding subsequently traverses those clauses a second time.  An executable
hardness compiler should instead stream the native natural fields directly.

This file gives every gate an exact native-field block and defines a direct
structural compiler whose state consists only of the next fresh atom, its root,
and the accumulated flat fields.  The main theorem identifies that stream with
the existing verified `formulaFields` representation exactly.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- The four native fields of a desired value on one transition wire. -/
def transitionLiteralFields (wire : TransitionWire) (desired : Bool) :
    List Nat :=
  [wire.atom,
    match wire.slice with
    | .current => 0
    | .next => 2,
    0,
    if desired then 1 else 0]

@[simp]
theorem transitionLiteralFields_eq_literalFields
    (wire : TransitionWire) (desired : Bool) :
    transitionLiteralFields wire desired =
      PeriodicCNFFlatEncoding.literalFields (wire.literal desired) := by
  rcases wire with ⟨slice, atom⟩
  cases slice <;> cases desired <;> rfl

/-- Native fields of one clause described directly by its desired wires. -/
def transitionClauseFields
    (literals : List (TransitionWire × Bool)) : List Nat :=
  literals.length :: literals.flatMap fun literal =>
    transitionLiteralFields literal.1 literal.2

theorem transitionClauseFields_eq_clauseFields
    (literals : List (TransitionWire × Bool)) :
    transitionClauseFields literals =
      PeriodicCNFFlatEncoding.clauseFields
        (literals.map fun literal => literal.1.literal literal.2) := by
  simp [transitionClauseFields, PeriodicCNFFlatEncoding.clauseFields,
    List.flatMap_map,
    transitionLiteralFields_eq_literalFields]

/-- Direct field block for a constant gate. -/
def constantGateFields (output : Nat) (value : Bool) : List Nat :=
  transitionClauseFields [(gateOutput output, value)]

/-- Direct field block for an equality gate. -/
def equalityGateFields (output : Nat) (input : TransitionWire) : List Nat :=
  transitionClauseFields [(gateOutput output, false), (input, true)] ++
    transitionClauseFields [(gateOutput output, true), (input, false)]

/-- Direct field block for a negation gate. -/
def notGateFields (output : Nat) (input : TransitionWire) : List Nat :=
  transitionClauseFields [(gateOutput output, false), (input, false)] ++
    transitionClauseFields [(gateOutput output, true), (input, true)]

/-- Direct field block for a conjunction gate. -/
def andGateFields (output : Nat) (first second : TransitionWire) : List Nat :=
  transitionClauseFields [(gateOutput output, false), (first, true)] ++
    transitionClauseFields [(gateOutput output, false), (second, true)] ++
    transitionClauseFields
      [(gateOutput output, true), (first, false), (second, false)]

/-- Direct field block for a disjunction gate. -/
def orGateFields (output : Nat) (first second : TransitionWire) : List Nat :=
  transitionClauseFields [(gateOutput output, true), (first, false)] ++
    transitionClauseFields [(gateOutput output, true), (second, false)] ++
    transitionClauseFields
      [(gateOutput output, false), (first, true), (second, true)]

@[simp]
theorem constantGateFields_eq (output : Nat) (value : Bool) :
    constantGateFields output value =
      (constantClauses output value).flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  simp [constantGateFields, constantClauses,
    transitionClauseFields_eq_clauseFields]

@[simp]
theorem equalityGateFields_eq (output : Nat) (input : TransitionWire) :
    equalityGateFields output input =
      (equalityClauses output input).flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  simp [equalityGateFields, equalityClauses,
    transitionClauseFields_eq_clauseFields]

@[simp]
theorem notGateFields_eq (output : Nat) (input : TransitionWire) :
    notGateFields output input =
      (notClauses output input).flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  simp [notGateFields, notClauses,
    transitionClauseFields_eq_clauseFields]

@[simp]
theorem andGateFields_eq (output : Nat)
    (first second : TransitionWire) :
    andGateFields output first second =
      (andClauses output first second).flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  simp [andGateFields, andClauses,
    transitionClauseFields_eq_clauseFields]

@[simp]
theorem orGateFields_eq (output : Nat)
    (first second : TransitionWire) :
    orGateFields output first second =
      (orClauses output first second).flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  simp [orGateFields, orClauses,
    transitionClauseFields_eq_clauseFields]

/-- Field-stream analogue of `CompiledTransitionExpr`. -/
structure CompiledTransitionFields where
  nextFresh : Nat
  root : Nat
  fields : List Nat
  deriving DecidableEq, Repr

/-- Structural Tseitin compilation directly to clause fields. -/
def compileTransitionFields :
    TransitionExpr → Nat → CompiledTransitionFields
  | .constant value, fresh =>
      ⟨fresh + 1, fresh, constantGateFields fresh value⟩
  | .wire input, fresh =>
      ⟨fresh + 1, fresh, equalityGateFields fresh input⟩
  | .not input, fresh =>
      let compiled := compileTransitionFields input fresh
      ⟨compiled.nextFresh + 1, compiled.nextFresh,
        compiled.fields ++
          notGateFields compiled.nextFresh (gateOutput compiled.root)⟩
  | .and first second, fresh =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
        firstCompiled.fields ++ secondCompiled.fields ++
          andGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)⟩
  | .or first second, fresh =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
        firstCompiled.fields ++ secondCompiled.fields ++
          orGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)⟩

@[simp]
theorem compileTransitionFields_nextFresh
    (expression : TransitionExpr) (fresh : Nat) :
    (compileTransitionFields expression fresh).nextFresh =
      (compileTransitionExpr expression fresh).nextFresh := by
  induction expression generalizing fresh with
  | constant value => rfl
  | wire input => rfl
  | not input induction =>
      simp [compileTransitionFields, compileTransitionExpr, induction]
  | and first second firstIH secondIH =>
      simp [compileTransitionFields, compileTransitionExpr,
        firstIH, secondIH]
  | or first second firstIH secondIH =>
      simp [compileTransitionFields, compileTransitionExpr,
        firstIH, secondIH]

@[simp]
theorem compileTransitionFields_root
    (expression : TransitionExpr) (fresh : Nat) :
    (compileTransitionFields expression fresh).root =
      (compileTransitionExpr expression fresh).root := by
  cases expression <;>
    simp [compileTransitionFields, compileTransitionExpr,
      compileTransitionFields_nextFresh]

theorem compileTransitionFields_fields
    (expression : TransitionExpr) (fresh : Nat) :
    (compileTransitionFields expression fresh).fields =
      (compileTransitionExpr expression fresh).clauses.flatMap
        PeriodicCNFFlatEncoding.clauseFields := by
  induction expression generalizing fresh with
  | constant value =>
      simp [compileTransitionFields, compileTransitionExpr]
  | wire input =>
      simp [compileTransitionFields, compileTransitionExpr]
  | not input induction =>
      simp [compileTransitionFields, compileTransitionExpr, induction,
        compileTransitionFields_nextFresh, compileTransitionFields_root]
  | and first second firstIH secondIH =>
      simp [compileTransitionFields, compileTransitionExpr,
        firstIH, secondIH, compileTransitionFields_nextFresh,
        compileTransitionFields_root]
  | or first second firstIH secondIH =>
      simp [compileTransitionFields, compileTransitionExpr,
        firstIH, secondIH, compileTransitionFields_nextFresh,
        compileTransitionFields_root]

/-- Complete flat formula fields, including the clause-count header and the
unit clause that forces the compiled root. -/
def requireTransitionExprFields
    (expression : TransitionExpr) (fresh : Nat) : List Nat :=
  (expression.clauseCount + 1) ::
    (compileTransitionFields expression fresh).fields ++
      constantGateFields
        (compileTransitionFields expression fresh).root true

/-- Streaming the direct fields is exactly the existing verified flat
representation of the required transition expression. -/
theorem requireTransitionExprFields_eq_formulaFields
    (expression : TransitionExpr) (fresh : Nat) :
    requireTransitionExprFields expression fresh =
      PeriodicCNFFlatEncoding.formulaFields
        (requireTransitionExpr expression fresh) := by
  simp [requireTransitionExprFields,
    PeriodicCNFFlatEncoding.formulaFields, requireTransitionExpr,
    compileTransitionFields_fields, compileTransitionFields_root,
    constantClauses]

end PeriodicCNF
end LeanTrominoes
