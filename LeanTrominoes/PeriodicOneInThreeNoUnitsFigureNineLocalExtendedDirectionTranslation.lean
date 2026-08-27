/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler
import LeanTrominoes.RetainedRayRasterizationTranslation

/-! # Translation invariance of finite Figure 9 prefix blocks -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Gadget PeriodicOrthocrossing

/-- Translating a selected local template route leaves its normalized finite
direction block unchanged. -/
theorem normalizedTranslatedLocalRoute_directionWord
    (profile :
      PeriodicCNF.UnaryProgramClauseProfile.ClauseProfile)
    (templateIndex :
      Fin (templateDrawingOfClauseProfile profile).incidences.length)
    (origin : Cell)
    (actualLocalRoute : List Cell)
    (localRouteEq :
      actualLocalRoute =
        translatePolyline origin
          ((templateDrawingOfClauseProfile profile).routeAt
            ((templateDrawingOfClauseProfile profile).incidenceAt
              templateIndex)))
    (actualLocalRouteNonempty : actualLocalRoute ≠ [])
    (actualLocalRouteOrthogonal : OrthogonalPolyline actualLocalRoute) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline actualLocalRoute) =
      normalizedLocalDirectionBlock ⟨profile, templateIndex⟩ := by
  let templateLocalRoute :=
    (templateDrawingOfClauseProfile profile).routeAt
      ((templateDrawingOfClauseProfile profile).incidenceAt templateIndex)
  have templateLocalRouteNonempty : templateLocalRoute ≠ [] := by
    intro empty
    apply actualLocalRouteNonempty
    rw [localRouteEq]
    change translatePolyline origin templateLocalRoute = []
    rw [empty]
    rfl
  have translatedTemplateLocalRouteOrthogonal :
      OrthogonalPolyline
        (translatePolyline origin templateLocalRoute) := by
    rw [← localRouteEq]
    exact actualLocalRouteOrthogonal
  have templateLocalRouteOrthogonal :
      OrthogonalPolyline templateLocalRoute :=
    translatedTemplateLocalRouteOrthogonal.of_translate origin
  rw [localRouteEq]
  unfold translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    templateLocalRouteNonempty templateLocalRouteOrthogonal origin]
  change unitSubdivisionDirections
      (translatePolyline origin
        (AxisDirection.normalizeOrthogonalPolyline templateLocalRoute)) = _
  rw [unitSubdivisionDirections_translatePolyline]
  rfl

/-- A translated local template route joined to the equally translated
extended connector has exactly its finite normalized profile block. -/
theorem normalizedTranslatedLocalExtendedRoute_directionWord
    (profile :
      PeriodicCNF.UnaryProgramClauseProfile.ClauseProfile)
    (templateIndex :
      Fin (templateDrawingOfClauseProfile profile).incidences.length)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (origin : Cell)
    (actualLocalRoute : List Cell)
    (localRouteEq :
      actualLocalRoute =
        translatePolyline origin
          ((templateDrawingOfClauseProfile profile).routeAt
            ((templateDrawingOfClauseProfile profile).incidenceAt
              templateIndex)))
    (actualPrefixNonempty :
      joinAtEndpoint actualLocalRoute
          (data.translatedExtendedRoute origin slot) ≠ [])
    (actualPrefixOrthogonal :
      OrthogonalPolyline
        (joinAtEndpoint actualLocalRoute
          (data.translatedExtendedRoute origin slot))) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint actualLocalRoute
            (data.translatedExtendedRoute origin slot))) =
      normalizedLocalExtendedDirectionBlock
        ⟨profile, templateIndex, data, slot⟩ := by
  let templateLocalRoute :=
    (templateDrawingOfClauseProfile profile).routeAt
      ((templateDrawingOfClauseProfile profile).incidenceAt templateIndex)
  let templatePrefix :=
    joinAtEndpoint templateLocalRoute (data.extendedRoute slot)
  have actualPrefixEq :
      joinAtEndpoint actualLocalRoute
          (data.translatedExtendedRoute origin slot) =
        translatePolyline origin templatePrefix := by
    rw [localRouteEq]
    unfold ComposedClauseExitFanData.translatedExtendedRoute
    exact (translatePolyline_joinAtEndpoint
      origin templateLocalRoute (data.extendedRoute slot)).symm
  have templatePrefixNonempty : templatePrefix ≠ [] := by
    intro empty
    apply actualPrefixNonempty
    rw [actualPrefixEq, empty]
    rfl
  have translatedTemplatePrefixOrthogonal :
      OrthogonalPolyline (translatePolyline origin templatePrefix) := by
    rw [← actualPrefixEq]
    exact actualPrefixOrthogonal
  have templatePrefixOrthogonal : OrthogonalPolyline templatePrefix :=
    translatedTemplatePrefixOrthogonal.of_translate origin
  rw [actualPrefixEq]
  unfold translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    templatePrefixNonempty templatePrefixOrthogonal origin]
  change unitSubdivisionDirections
      (translatePolyline origin
        (AxisDirection.normalizeOrthogonalPolyline templatePrefix)) = _
  rw [unitSubdivisionDirections_translatePolyline]
  rfl

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
