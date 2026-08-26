/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyData
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices

/-! # First-occurrence lookup of normalized routed-variable descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Looking up the descriptor at the first occurrence of one normalized
routed-variable implication returns the finite descriptor classified by its
normalized link and direction. -/
theorem normalizedRoutedVariableClauseDescriptors_getElem?_idxOf
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool)
    (taggedLinkMember : taggedLink ∈
      ((drawingRoutedVariableLinks source).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source))).product
        [true, false]) :
    (normalizedRoutedVariableClauseDescriptors source)[
        (routedVariableMetadataNormalizedClauses source).idxOf
          (PeriodicEquality.normalizedClause taggedLink)]? =
      some (normalizedRoutedVariableClauseDescriptor taggedLink) := by
  rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq]
  unfold normalizedRoutedVariableClauseDescriptors
  let taggedLinks :=
    ((drawingRoutedVariableLinks source).map
      (PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source))).product
      [true, false]
  change (taggedLinks.map normalizedRoutedVariableClauseDescriptor)[
      (taggedLinks.map PeriodicEquality.normalizedClause).idxOf
        (PeriodicEquality.normalizedClause taggedLink)]? = _
  have normalizedClauseMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        taggedLinks.map PeriodicEquality.normalizedClause :=
    List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have clauseLookup :=
    List.getElem?_idxOf normalizedClauseMember
  rw [List.getElem?_map] at clauseLookup
  cases taggedLookup : taggedLinks[
      (taggedLinks.map PeriodicEquality.normalizedClause).idxOf
        (PeriodicEquality.normalizedClause taggedLink)]? with
  | none =>
      simp [taggedLookup] at clauseLookup
  | some selected =>
      have selectedClauseEq :
          PeriodicEquality.normalizedClause selected =
            PeriodicEquality.normalizedClause taggedLink := by
        simpa [taggedLookup] using clauseLookup
      have selectedEq :=
        PeriodicEquality.normalizedClause_injective selectedClauseEq
      subst selected
      rw [List.getElem?_map, taggedLookup]
      rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
