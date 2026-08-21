/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFRouteDescriptorRenaming
import LeanTrominoes.PeriodicThreeSATThreeCycleRenaming
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Occurrence splitting and numeric routes under atom renaming -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The complete occurrence-split formula commutes with an injective source
atom rename. -/
theorem formula_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) :
    formula (source.rename variableMap) =
      (formula source).rename (renameOccurrence variableMap) := by
  unfold formula
  rw [occurrenceClauses_rename,
    allCycleClauses_rename_of_injective variableMap injective source]
  unfold PeriodicCNF.rename
  rw [List.map_append]

/-- Numeric routes of an occurrence-split formula are unchanged by an
injective rename of the pre-split atoms. -/
theorem numericRouteDescriptors_formula_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) :
    PeriodicCNF.numericRouteDescriptors
        (formula (source.rename variableMap)) =
      PeriodicCNF.numericRouteDescriptors (formula source) := by
  rw [formula_rename_of_injective variableMap injective source]
  exact PeriodicCNF.numericRouteDescriptors_rename_of_injective
    (renameOccurrence variableMap)
    (renameOccurrence_injective variableMap injective)
    (formula source)

/-- The explicit copied-plus-cycle descriptor stream likewise depends only
on the source presentation's atom-equality pattern. -/
theorem splitRouteDescriptors_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) :
    splitRouteDescriptors (source.rename variableMap) =
      splitRouteDescriptors source := by
  rw [← numericRouteDescriptors_formula_eq_splitRouteDescriptors,
    ← numericRouteDescriptors_formula_eq_splitRouteDescriptors]
  exact numericRouteDescriptors_formula_rename_of_injective
    variableMap injective source

end PeriodicThreeSATThree
end LeanTrominoes
