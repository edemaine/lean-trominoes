/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseNormalization
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizationInjectivity
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedFamilyData

/-! # Duplicate-freedom of normalized retained-carrier metadata -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The metadata presentation of normalized carrier clauses is exactly the
generic normalized equality family over the wrapped endpoint normalization. -/
theorem carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    carrierMetadataNormalizedClauses source =
      PeriodicEquality.normalizedFormulaClauses
        (carrierWrappedVariableNormalization source)
        (retainedDrawingCompleteCarrierLinks
          source.incidenceGraph) := by
  unfold carrierMetadataNormalizedClauses
    retainedDrawingPlanarSATCarrierClauseMetadata
  rw [List.map_flatMap,
    PeriodicEquality.normalizedFormulaClauses_eq]
  induction retainedDrawingCompleteCarrierLinks
      source.incidenceGraph with
  | nil => rfl
  | cons link links induction =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [carrierLink_normalizedClauses_eq]
      simp [List.product, induction]

/-- No carrier clause is removed by final clause deduplication. -/
theorem carrierMetadataNormalizedClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (carrierMetadataNormalizedClauses source).Nodup := by
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses]
  exact retainedCarrierWrappedNormalizedFormulaClauses_nodup source

@[simp] theorem carrierMetadataNormalizedClauses_dedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (carrierMetadataNormalizedClauses source).dedup =
      carrierMetadataNormalizedClauses source :=
  List.dedup_eq_self.mpr (carrierMetadataNormalizedClauses_nodup source)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
