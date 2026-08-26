/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeNonCrossoverNormalizedDeduplication

/-! # Complete five-family normalized clause presentation -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Shared structural equality used at the five-family semantic boundary. -/
abbrev fiveFamilyNormalizedThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fun first second => instDecidableEqProd first second

/-- The duplicate-free retained clauses of a valid occurrence-split source
are exactly the crossover, carrier, bend, routed-clause, and routed-variable
families in that order. -/
theorem deduplicatedClauses_formula_eq_fiveFamilies
    {Variable : Type} [DecidableEq Variable]
    [occurrenceDecEq : DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := formula source
    deduplicatedClauses retained =
      (crossoverMetadataNormalizedClausesDedup retained ++
        formulaCarrierMetadataNormalizedClauses source) ++
      ((formulaBaseBendNormalizedClauses source ++
        formulaBaseRoutedClauseNormalizedClauses source) ++
        formulaCanonicalWrappedNormalizedRoutedVariableClauses source) := by
  have occurrenceDecEqEq : occurrenceDecEq =
      fiveFamilyNormalizedThreeOccurrenceDecidableEq :=
    Subsingleton.elim _ _
  subst occurrenceDecEq
  dsimp only
  rw [deduplicatedClauses_eq_named_crossover_append_nonCrossover
    (formula source)
    (formula_incidenceGraph_isWellFormed source)
    (formula_incidenceGraph_degreeAtMostThree sourceWidth)
    (formula_incidenceGraph_isLocal sourceLocal)]
  have suffixEq :
      nonCrossoverMetadataNormalizedClausesDedup (formula source) =
        formulaNonCrossoverMetadataNormalizedClausesDedup source := by
    rfl
  rw [suffixEq,
    formulaNonCrossoverMetadataNormalizedClausesDedup_eq_families
      source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets]
  simp only [List.append_assoc]

/-- Bend-focused reassociation of the five-family presentation, exposing
the crossover/carrier prefix and routed suffix as opaque list boundaries. -/
theorem deduplicatedClauses_formula_eq_bendFamily
    {Variable : Type} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := formula source
    deduplicatedClauses retained =
      ((crossoverMetadataNormalizedClausesDedup retained ++
        formulaCarrierMetadataNormalizedClauses source) ++
        formulaBaseBendNormalizedClauses source) ++
      (formulaBaseRoutedClauseNormalizedClauses source ++
        formulaCanonicalWrappedNormalizedRoutedVariableClauses source) := by
  simpa only [List.append_assoc] using
    deduplicatedClauses_formula_eq_fiveFamilies
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets

/-- Routed-clause-focused reassociation of the five-family presentation,
exposing the crossover/carrier/bend prefix and routed-variable suffix. -/
theorem deduplicatedClauses_formula_eq_routedClauseFamily
    {Variable : Type} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := formula source
    deduplicatedClauses retained =
      (((crossoverMetadataNormalizedClausesDedup retained ++
        formulaCarrierMetadataNormalizedClauses source) ++
        formulaBaseBendNormalizedClauses source) ++
        formulaBaseRoutedClauseNormalizedClauses source) ++
      formulaCanonicalWrappedNormalizedRoutedVariableClauses source := by
  simpa only [List.append_assoc] using
    deduplicatedClauses_formula_eq_fiveFamilies
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets

end LeanTrominoes.PeriodicThreeSATThree
