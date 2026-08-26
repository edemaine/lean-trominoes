/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedLinks

/-! # Canonical normalized routed-variable clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance canonicalRoutedVariableWrappedDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable)) :=
  inferInstance

/-- Both normalized implication clauses of every canonical final-site link. -/
def canonicalWrappedNormalizedRoutedVariableClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))) :=
  ((canonicalWrappedNormalizedRoutedVariableLinks source).product
    [true, false]).map PeriodicEquality.normalizedClause

/-- Stable clause deduplication of the routed-variable family retains
exactly the canonical final-site implication pairs. -/
theorem routedVariableMetadataNormalizedClauses_formula_dedup_eq_canonical
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (routedVariableMetadataNormalizedClauses
        (formula source)).dedup =
      canonicalWrappedNormalizedRoutedVariableClauses source := by
  rw [routedVariableMetadataNormalizedClauses_dedup_eq_wrappedLinks]
  unfold deduplicatedWrappedNormalizedRoutedVariableClauses
    canonicalWrappedNormalizedRoutedVariableClauses
  rw [
    deduplicatedWrappedNormalizedRoutedVariableLinks_formula_eq_canonical
      source positiveOffsets]

/-- The canonical routed-variable clause list is duplicate-free. -/
theorem canonicalWrappedNormalizedRoutedVariableClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (canonicalWrappedNormalizedRoutedVariableClauses source).Nodup := by
  rw [←
    routedVariableMetadataNormalizedClauses_formula_dedup_eq_canonical
      source positiveOffsets]
  exact List.nodup_dedup _

end PeriodicThreeSATThree
end LeanTrominoes

end
