/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedFamilyData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseNormalization

/-! # Normalized routed-variable metadata as an equality family -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The metadata presentation of normalized routed-variable clauses is
exactly the generic normalized equality family over the active links. -/
theorem routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariableMetadataNormalizedClauses source =
      PeriodicEquality.normalizedFormulaClauses
        (externalWrappedVariableNormalization source)
        (drawingRoutedVariableLinks source) := by
  unfold routedVariableMetadataNormalizedClauses
    drawingPlanarSATRoutedVariableClauseMetadata
  rw [List.map_flatMap,
    PeriodicEquality.normalizedFormulaClauses_eq]
  calc
    (drawingVariableRouteSites source).flatMap (fun site =>
        ((routedVariableLinksAt source site).zipIdx.flatMap
          (fun taggedLink =>
            drawingPlanarSATRoutedVariableClauseMetadataFor
              site taggedLink.2 taggedLink.1.first.duplicatorArm
                taggedLink.1)).map (normalizedClause source)) =
      (drawingVariableRouteSites source).flatMap (fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap
          (fun taggedLink =>
            (([PeriodicEquality.normalizeLink
                (externalWrappedVariableNormalization source)
                taggedLink.1].product [true, false]).map
              PeriodicEquality.normalizedClause))) := by
        apply List.flatMap_congr
        intro site _siteMember
        rw [List.map_flatMap]
        apply List.flatMap_congr
        intro taggedLink _taggedLinkMember
        exact routedVariableLink_normalizedClauses_eq
          source site taggedLink.2
            taggedLink.1.first.duplicatorArm taggedLink.1
    _ = List.map PeriodicEquality.normalizedClause
        (List.product
          ((drawingRoutedVariableLinks source).map
            (PeriodicEquality.normalizeLink
              (externalWrappedVariableNormalization source)))
          [true, false]) := by
        unfold drawingRoutedVariableLinks
        let block := fun link : EqualityLink (PlanarSATNode Variable) =>
          (([PeriodicEquality.normalizeLink
              (externalWrappedVariableNormalization source) link].product
            [true, false]).map PeriodicEquality.normalizedClause)
        change (drawingVariableRouteSites source).flatMap (fun site =>
            (routedVariableLinksAt source site).zipIdx.flatMap
              (fun taggedLink => block taggedLink.1)) = _
        calc
          _ = (drawingVariableRouteSites source).flatMap (fun site =>
              (routedVariableLinksAt source site).flatMap block) := by
                apply List.flatMap_congr
                intro site _siteMember
                exact PeriodicCNF.zipIdx_flatMap_fst block
                  (routedVariableLinksAt source site) 0
          _ = ((drawingVariableRouteSites source).flatMap
              (routedVariableLinksAt source)).flatMap block := by
                rw [List.flatMap_assoc]
          _ = _ := by
                induction (drawingVariableRouteSites source).flatMap
                    (routedVariableLinksAt source) with
                | nil => rfl
                | cons link links induction =>
                    simp only [List.flatMap_cons, List.map_cons]
                    rw [induction]
                    simp [block, List.product]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
