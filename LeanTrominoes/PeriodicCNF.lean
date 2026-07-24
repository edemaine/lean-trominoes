import LeanTrominoes.Basic

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
