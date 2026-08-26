/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyData
import LeanTrominoes.PeriodicEqualityNormalizedFormulaDeduplication

/-! # Exact deduplication of normalized routed-variable metadata -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Wrapped normalized routed-variable links in stable last-representative
order. -/
def deduplicatedWrappedNormalizedRoutedVariableLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)) :=
  ((drawingRoutedVariableLinks source).map
    (PeriodicEquality.normalizeLink
      (externalWrappedVariableNormalization source))).dedup

/-- The canonical clause stream induced by the deduplicated wrapped links. -/
def deduplicatedWrappedNormalizedRoutedVariableClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  ((deduplicatedWrappedNormalizedRoutedVariableLinks source).product
    [true, false]).map PeriodicEquality.normalizedClause

/-- Stable clause deduplication removes exactly the duplicate normalized
links and retains both implication clauses of every surviving link. -/
theorem routedVariableMetadataNormalizedClauses_dedup_eq_wrappedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (routedVariableMetadataNormalizedClauses source).dedup =
      deduplicatedWrappedNormalizedRoutedVariableClauses source := by
  rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.dedup_normalizedFormulaClauses_eq]
  rfl

/-- The canonical wrapped routed-variable clause stream is duplicate-free. -/
theorem deduplicatedWrappedNormalizedRoutedVariableClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (deduplicatedWrappedNormalizedRoutedVariableClauses source).Nodup := by
  rw [← routedVariableMetadataNormalizedClauses_dedup_eq_wrappedLinks]
  exact List.nodup_dedup _

@[simp] theorem deduplicatedWrappedNormalizedRoutedVariableClauses_dedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (deduplicatedWrappedNormalizedRoutedVariableClauses source).dedup =
      deduplicatedWrappedNormalizedRoutedVariableClauses source :=
  List.dedup_eq_self.mpr
    (deduplicatedWrappedNormalizedRoutedVariableClauses_nodup source)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
