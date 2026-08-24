/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Basic
import LeanTrominoes.PeriodicCNFCoreData
import Mathlib.Computability.Primrec.List

/-!
# Periodic CNF formulas

This file defines the local, translation-invariant Boolean constraint systems
used as an intermediate source problem in the hardness proof of Theorem 5.2.
A finite formula is imposed at every translate of the integer lattice.
-/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- Product representation used by the standard computability encoding. -/
def equivData {Variable : Type*} :
    PeriodicLiteral Variable ≃ Variable × Cell × Bool where
  toFun literal := (literal.atom, literal.offset, literal.value)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv literal := by cases literal; rfl
  right_inv data := by rcases data with ⟨atom, offset, value⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PeriodicLiteral Variable) :=
  Primcodable.ofEquiv (Variable × Cell × Bool) equivData

theorem equivData_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData : PeriodicLiteral Variable → Variable × Cell × Bool) :=
  Primrec.of_equiv

theorem equivData_symm_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData.symm :
      Variable × Cell × Bool → PeriodicLiteral Variable) :=
  Primrec.of_equiv_symm

/-- Whether a literal holds at one translate under a plane-wide assignment. -/
def Holds {Variable : Type*} (assignment : Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable) : Prop :=
  assignment literal.atom (Cell.add translate literal.offset) = literal.value

end PeriodicLiteral

namespace PeriodicClause

/-- Manhattan distance between the offsets of two literals. -/
def offsetDistance {Variable : Type*}
    (first second : PeriodicLiteral Variable) : Nat :=
  (first.offset.1 - second.offset.1).natAbs +
    (first.offset.2 - second.offset.2).natAbs

/-- A protoclauses is local when every two offsets in it are at Manhattan
distance at most one, matching the paper's definition. -/
def IsLocal {Variable : Type*} (clause : PeriodicClause Variable) : Prop :=
  ∀ first ∈ clause, ∀ second ∈ clause, offsetDistance first second ≤ 1

/-- A width bound on one local clause. -/
def WidthAtMost {Variable : Type*}
    (width : Nat) (clause : PeriodicClause Variable) : Prop :=
  clause.length ≤ width

/-- Whether at least one literal in a local clause holds at one translate. -/
def Holds {Variable : Type*} (assignment : Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable) : Prop :=
  ∃ literal ∈ clause, literal.Holds assignment translate

end PeriodicClause

namespace PeriodicCNF

/-- List representation used by the standard computability encoding. -/
def equivData {Variable : Type*} :
    PeriodicCNF Variable ≃ List (PeriodicClause Variable) where
  toFun formula := formula.clauses
  invFun clauses := ⟨clauses⟩
  left_inv formula := by cases formula; rfl
  right_inv _ := rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PeriodicCNF Variable) :=
  Primcodable.ofEquiv (List (PeriodicClause Variable)) equivData

theorem equivData_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData : PeriodicCNF Variable → List (PeriodicClause Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData.symm :
      List (PeriodicClause Variable) → PeriodicCNF Variable) :=
  Primrec.of_equiv_symm

/-- Every protoclauses in the finite presentation is local. -/
def IsLocal {Variable : Type*} (formula : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, clause.IsLocal

/-- Every protoclauses has at most the specified number of literals. -/
def WidthAtMost {Variable : Type*}
    (width : Nat) (formula : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, clause.WidthAtMost width

/-- Whether an assignment satisfies every clause at every lattice translate. -/
def Satisfies {Variable : Type*} (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) : Prop :=
  ∀ translate clause, clause ∈ formula.clauses →
    clause.Holds assignment translate

/-- Whether a periodic CNF formula has a plane-wide satisfying assignment. -/
def Satisfiable {Variable : Type*} (formula : PeriodicCNF Variable) : Prop :=
  ∃ assignment : Variable → Cell → Bool, formula.Satisfies assignment

end PeriodicCNF

end LeanTrominoes
