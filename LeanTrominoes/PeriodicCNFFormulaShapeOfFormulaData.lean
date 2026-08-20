/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeData

/-! # Canonical finite shapes of concrete periodic CNF formulas -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeOfFormula

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

/-- Package a nonempty list of at most three literal profiles.  The fallback
branches make the operation total; the semantic theorem below eliminates
them for the certified formulas used by the reduction. -/
def clauseProfile : List LiteralProfile → ClauseProfile
  | [] => default
  | [first] => .unary first
  | [first, second] => .binary first second
  | first :: second :: third :: _ => .ternary first second third

/-- Clause profiles in presentation order. -/
def profiles {Variable : Type} (formula : PeriodicCNF Variable) :
    List ClauseProfile :=
  formula.clauses.map fun clause =>
    clauseProfile (literalProfiles clause)

/-- Canonical shape of a concrete finite periodic-CNF presentation: clauses
remain in presentation order and the suffix has one marker per distinct
variable. -/
def shape {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List FormulaShape.Token :=
  (profiles formula).map .clause ++
    List.replicate formula.variableOccurrences.dedup.length .variable

@[simp] theorem clauseProfiles_shape
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaShape.clauseProfiles (shape formula) =
      profiles formula := by
  simp [shape]

@[simp] theorem variableCount_shape
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaShape.variableCount (shape formula) =
      formula.variableOccurrences.dedup.length := by
  simp [shape, FormulaShape.variableCount]

end FormulaShapeOfFormula
end PeriodicCNF
end LeanTrominoes
