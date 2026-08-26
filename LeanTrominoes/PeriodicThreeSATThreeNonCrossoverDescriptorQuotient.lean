/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierRepresentativeDescriptors
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedClauseRepresentativeDescriptors
import LeanTrominoes.PeriodicThreeSATThreeCanonicalRoutedVariableDescriptorQuotient
import LeanTrominoes.PeriodicThreeSATThreeNonCrossoverNormalizedDeduplication

/-! # Public descriptor quotient of the non-crossover suffix -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance nonCrossoverDescriptorWrappedDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable)) :=
  inferInstance

/-- Canonical finite descriptor stream of the four non-crossover families
under an explicit equality implementation for occurrence-split variables. -/
def nonCrossoverDescriptorQuotientWith
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (outputDecidableEq : DecidableEq
      (ThreeOccurrenceVariable Variable)) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  letI := outputDecidableEq
  carrierMetadataClauseDescriptors (formula source) ++
    (baseBendClauseDescriptors (formula source) ++
      (baseRoutedClauseDescriptors (formula source) ++
        (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
            (fun _targetIndex => routedVariableFullSiteBlock)))

/-- Canonical finite descriptor stream of the four non-crossover families:
injective carriers, untranslated bends, one source-clause copy, and one
complete routed-variable site per source literal occurrence. -/
def nonCrossoverDescriptorQuotient
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  nonCrossoverDescriptorQuotientWith source inferInstance

/-- The non-crossover quotient is independent of the chosen decidable
equality implementation for occurrence-split variables. -/
theorem nonCrossoverDescriptorQuotientWith_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : DecidableEq
      (ThreeOccurrenceVariable Variable)) :
    nonCrossoverDescriptorQuotientWith source first =
      nonCrossoverDescriptorQuotientWith source second := by
  have instanceEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- The default non-crossover quotient agrees with every explicit equality
implementation. -/
theorem nonCrossoverDescriptorQuotient_eq_with
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (outputDecidableEq : DecidableEq
      (ThreeOccurrenceVariable Variable)) :
    nonCrossoverDescriptorQuotient source =
      nonCrossoverDescriptorQuotientWith source outputDecidableEq := by
  unfold nonCrossoverDescriptorQuotient
  exact nonCrossoverDescriptorQuotientWith_eq source _ _

/-- Mapping public representative selection over the deduplicated
non-crossover suffix gives exactly its four canonical finite blocks. -/
theorem nonCrossoverMetadataNormalizedClauses_formula_dedup_map_representative
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    ((nonCrossoverMetadataNormalizedClauses (formula source)).dedup).map
        (representativeClauseDescriptor (formula source)) =
      nonCrossoverDescriptorQuotient source := by
  unfold nonCrossoverDescriptorQuotient
    nonCrossoverDescriptorQuotientWith
  rw [nonCrossoverMetadataNormalizedClauses_formula_dedup_eq
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]
  simp only [List.map_append]
  rw [carrierMetadataNormalizedClauses_map_representative_eq_descriptors
      (formula source)
      (formula_incidenceGraph_isWellFormed source)
      (formula_incidenceGraph_degreeAtMostThree sourceWidth)
      (formula_incidenceGraph_isLocal sourceLocal),
    baseBendNormalizedClauses_map_representative_eq_descriptors
      (formula source)
      (formula_incidenceGraph_isWellFormed source)
      (formula_incidenceGraph_degreeAtMostThree sourceWidth)
      (formula_incidenceGraph_isLocal sourceLocal),
    baseRoutedClauseNormalizedClauses_map_representative_eq_descriptors
      (formula source)
      (formula_incidenceGraph_isWellFormed source)
      (formula_incidenceGraph_degreeAtMostThree sourceWidth)
      (formula_incidenceGraph_isLocal sourceLocal)
      (formula_clausesNonempty source sourceClausesNonempty),
    canonicalRoutedVariableRepresentativeDescriptors_eq_fullSites
      source sourceLocal sourceWidth positiveOffsets]
  simp only [List.append_assoc]

end LeanTrominoes.PeriodicThreeSATThree
