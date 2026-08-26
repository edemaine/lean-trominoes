/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariableRepresentativeDescriptor
import LeanTrominoes.PeriodicThreeSATThreeGraph
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedClauses

/-! # Representative descriptors of canonical routed-variable clauses -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Mapping public representative selection over the canonical deduplicated
routed-variable clauses is the normalized-link descriptor map in the same
order. -/
theorem canonicalWrappedNormalizedRoutedVariableClauses_map_representative
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (canonicalWrappedNormalizedRoutedVariableClauses source).map
        (representativeClauseDescriptor (formula source)) =
      ((canonicalWrappedNormalizedRoutedVariableLinks source).product
        [true, false]).map normalizedRoutedVariableClauseDescriptor := by
  unfold canonicalWrappedNormalizedRoutedVariableClauses
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedLink taggedLinkMember
  simp only [Function.comp_apply]
  rcases List.mem_product.mp taggedLinkMember with
    ⟨normalizedLinkMember, directionMember⟩
  have rawNormalizedLinkMember :=
    canonicalWrappedNormalizedRoutedVariableLinks_subset_raw
      source positiveOffsets normalizedLinkMember
  have rawTaggedLinkMember : taggedLink ∈
      ((drawingRoutedVariableLinks (formula source)).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization (formula source)))).product
        [true, false] :=
    List.mem_product.mpr ⟨rawNormalizedLinkMember, directionMember⟩
  exact representativeClauseDescriptor_eq_normalizedRoutedVariable
    (formula source)
    (formula_incidenceGraph_isWellFormed source)
    (formula_incidenceGraph_degreeAtMostThree sourceWidth)
    (formula_incidenceGraph_isLocal sourceLocal)
    taggedLink rawTaggedLinkMember

end LeanTrominoes.PeriodicThreeSATThree
