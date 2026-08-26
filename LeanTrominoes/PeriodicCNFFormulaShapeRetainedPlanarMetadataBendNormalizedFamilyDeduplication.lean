/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendClauseNormalizationAt
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedLinkQuotient
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedFamilyData
import LeanTrominoes.PeriodicEqualityNormalizedFormulaDeduplication

/-! # Exact deduplication of normalized retained-bend metadata -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The two normalized metadata clauses of one bend are the generic forward
and backward clauses of its wrapped normalized link. -/
theorem bendLink_normalizedClauses_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (routeBend : RouteBend) :
    (drawingPlanarSATBendClauseMetadataFor
      (Variable := Variable) source.incidenceGraph routeBend).map
        (normalizedClause source) =
      (([wrappedNormalizedRouteBendLink source routeBend].product
        [true, false]).map PeriodicEquality.normalizedClause) := by
  rw [drawingPlanarSATBendClauseMetadataFor_eq_pair]
  simp only [List.map_cons, List.map_nil]
  rw [normalizedClause_bendClauseMetadataAt_eq
      source routeBend true,
    normalizedClause_bendClauseMetadataAt_eq
      source routeBend false]
  rfl

/-- The metadata presentation of normalized bend clauses is exactly the
generic normalized equality family over the semantic bend links. -/
theorem bendMetadataNormalizedClauses_eq_normalizedFormulaClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    bendMetadataNormalizedClauses source =
      PeriodicEquality.normalizedFormulaClauses
        (carrierWrappedVariableNormalization source)
        (drawingRouteBendLinks source.incidenceGraph) := by
  unfold bendMetadataNormalizedClauses
    drawingPlanarSATBendClauseMetadata drawingRouteBendLinks
  rw [List.map_flatMap,
    PeriodicEquality.normalizedFormulaClauses_eq]
  induction (drawingRouteBends source.incidenceGraph).dedup with
  | nil => rfl
  | cons routeBend routeBends induction =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [bendLink_normalizedClauses_eq, induction]
      rfl

/-- Canonical normalized bend clauses: one two-clause implication block for
each untranslated bend link in numeric route order. -/
def baseBendNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  ((baseBendNormalizedLinks source).product [true, false]).map
    PeriodicEquality.normalizedClause

/-- Stable clause deduplication removes precisely the translated copies of
the bend equalities. -/
theorem bendMetadataNormalizedClauses_dedup_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (bendMetadataNormalizedClauses source).dedup =
      baseBendNormalizedClauses source := by
  rw [bendMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.dedup_normalizedFormulaClauses_eq,
    drawingRouteBendLinks_wrappedNormalized_dedup_eq_base]
  rfl

/-- The canonical untranslated bend-clause stream is duplicate-free. -/
theorem baseBendNormalizedClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (baseBendNormalizedClauses source).Nodup := by
  rw [← bendMetadataNormalizedClauses_dedup_eq_base]
  exact List.nodup_dedup _

@[simp] theorem baseBendNormalizedClauses_dedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (baseBendNormalizedClauses source).dedup =
      baseBendNormalizedClauses source :=
  List.dedup_eq_self.mpr (baseBendNormalizedClauses_nodup source)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
