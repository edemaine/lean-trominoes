/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackNormalizedDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFinalBendScaledRouteEvidenceData

/-! # Directional extensionality for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Any scaled source route with the canonical bend prefix and terminal datum
normalizes to the exact finite bend-record word. -/
theorem bendRoute_normalized_fallback_directions_eq
    (firstPort secondPort : CornerPort)
    (different : firstPort ≠ secondPort)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (routeLength : 2 ≤ route.length)
    (routeClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (bendRouteTerminalData firstPort secondPort
            localClauseIndex literalIndex)))
    (routeOrthogonal : OrthogonalPolyline route)
    (routePrefixDirections :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.repeatDirections 1152
          (bendRoutePrefixDirections firstPort secondPort
            localClauseIndex literalIndex)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (bendRouteTerminalData firstPort secondPort
                localClauseIndex literalIndex))
            slot)) =
      bendRouteNormalizedFallbackDirections firstPort secondPort
        localClauseIndex literalIndex slot := by
  let baseRoute := cornerEqualityRoutes firstPort secondPort
    localClauseIndex literalIndex
  let template := scalePolyline retainedAngularFanSourceClearanceFactor
    baseRoute
  let terminal := scaleRetainedTerminalData
    retainedAngularFanSourceClearanceFactor
    (bendRouteTerminalData firstPort secondPort
      localClauseIndex literalIndex)
  have certificate := bendRouteCardinalTangentCertificate_of_ne
    firstPort secondPort different localClauseIndex literalIndex
      localClauseIndex.isLt literalIndex.isLt
  have templateLength : 2 ≤ template.length := by
    have baseLength : 2 ≤ baseRoute.length := by
      have certifiedLength : 3 ≤ baseRoute.length := by
        simpa only [baseRoute] using certificate.routeLength
      omega
    simpa [template, scalePolyline] using baseLength
  have templateClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector template) =
        some terminal := by
    exact routeTerminalVector_scale_classified
      retainedAngularFanSourceClearanceFactor_pos certificate.classified
  have templateOrthogonal : OrthogonalPolyline template := by
    exact certificate.routeOrthogonal.scalePolyline (by native_decide)
  have terminalPositive : 0 < terminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      certificate.terminalLengthPositive
  have valid : RetainedFallbackFanKind.ordinary.Valid terminal := by
    trivial
  have templatePrefixDirections :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix template) =
        Gadget.repeatDirections 1152
          (bendRoutePrefixDirections firstPort secondPort
            localClauseIndex literalIndex) := by
    dsimp only [template, baseRoute]
    rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
    rfl
  have prefixDirectionsEq :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix template) :=
    routePrefixDirections.trans templatePrefixDirections.symm
  calc
    _ = Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
              template terminal slot)) :=
      RetainedFallbackFanKind.splicedOwnFigure7Route_normalized_directions_eq_of_sourcePrefix_directions_eq
        .ordinary route template terminal slot routeLength templateLength
        routeClassified templateClassified routeOrthogonal templateOrthogonal
        terminalPositive valid prefixDirectionsEq
    _ = _ := by
      have finite :=
        scaledSplicedOwnFigure7Route_bend_translate_normalized_directions
          (0, 0) firstPort secondPort different
          localClauseIndex literalIndex localClauseIndex.isLt
          literalIndex.isLt slot
      simpa only [template, baseRoute, terminal,
        translatePolyline_zero] using finite

/-- The packaged source-route facts specialize bend extensionality in one
step. -/
theorem FinalBendScaledRouteEvidence.normalizedDirections
    (firstPort secondPort : CornerPort)
    (different : firstPort ≠ secondPort)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (evidence : FinalBendScaledRouteEvidence route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData firstPort secondPort
          localClauseIndex literalIndex))
      (Gadget.repeatDirections 1152
        (bendRoutePrefixDirections firstPort secondPort
          localClauseIndex literalIndex))) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (bendRouteTerminalData firstPort secondPort
                localClauseIndex literalIndex))
            slot)) =
      bendRouteNormalizedFallbackDirections firstPort secondPort
        localClauseIndex literalIndex slot :=
  bendRoute_normalized_fallback_directions_eq
    firstPort secondPort different localClauseIndex literalIndex slot route
    evidence.routeLength evidence.routeClassified evidence.routeOrthogonal
    evidence.routePrefixDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
