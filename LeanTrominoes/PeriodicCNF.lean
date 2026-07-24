import LeanTrominoes.Basic
import Mathlib.Computability.Primrec.List

/-!
# Periodic CNF formulas

This file defines the local, translation-invariant Boolean constraint systems
used as an intermediate source problem in the hardness proof of Theorem 5.2.
A finite formula is imposed at every translate of the integer lattice.
-/

namespace LeanTrominoes

/-- A Boolean literal names a variable, a lattice offset from the current
translate, and the value that makes the literal true. -/
structure PeriodicLiteral (Variable : Type*) where
  atom : Variable
  offset : Cell
  value : Bool
  deriving DecidableEq, Repr

/-- A local disjunction of periodic literals. -/
abbrev PeriodicClause (Variable : Type*) :=
  List (PeriodicLiteral Variable)

/-- A finite conjunction of local clauses, imposed at every lattice translate. -/
structure PeriodicCNF (Variable : Type*) where
  clauses : List (PeriodicClause Variable)
  deriving DecidableEq, Repr

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
