/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarIncidences

/-! # Atom renaming for periodic CNF presentations -/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- Rename one literal atom while preserving its offset and polarity. -/
def rename {Source Target : Type*} (variableMap : Source → Target)
    (literal : PeriodicLiteral Source) : PeriodicLiteral Target where
  atom := variableMap literal.atom
  offset := literal.offset
  value := literal.value

end PeriodicLiteral

namespace PeriodicCNF

/-- Rename every atom of one clause. -/
def renameClause {Source Target : Type*} (variableMap : Source → Target)
    (clause : PeriodicClause Source) : PeriodicClause Target :=
  clause.map (PeriodicLiteral.rename variableMap)

/-- Rename every atom of a periodic formula without changing presentation
order. -/
def rename {Source Target : Type*} (variableMap : Source → Target)
    (formula : PeriodicCNF Source) : PeriodicCNF Target where
  clauses := formula.clauses.map (renameClause variableMap)

end PeriodicCNF

namespace CNFIncidence

/-- Rename the atom data in one incidence metadata record. -/
def rename {Source Target : Type*} (variableMap : Source → Target)
    (incidence : CNFIncidence Source) : CNFIncidence Target where
  clauseIndex := incidence.clauseIndex
  clause := PeriodicCNF.renameClause variableMap incidence.clause
  literalIndex := incidence.literalIndex
  literal := PeriodicLiteral.rename variableMap incidence.literal

end CNFIncidence

end LeanTrominoes
