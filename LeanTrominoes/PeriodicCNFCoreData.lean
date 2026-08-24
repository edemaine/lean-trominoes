/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CellData

/-! # Core periodic-CNF data -/

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

/-- A finite conjunction of local clauses, imposed at every lattice
translate. -/
structure PeriodicCNF (Variable : Type*) where
  clauses : List (PeriodicClause Variable)
  deriving DecidableEq, Repr

end LeanTrominoes
