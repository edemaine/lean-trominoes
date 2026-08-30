/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentCertificate
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardTranslatedNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackCardinalTangentTranslatedNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData

/-! # Normalized direction words of finite bend fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Canonical normalized direction word of one source-clearance-scaled bend
fallback.  A forward tangent cancels the lane shift from both the end of the
source prefix and the start of the fan suffix; a backward tangent is a plain
concatenation. -/
def bendRouteNormalizedFallbackDirections
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  let sourceWord :=
    Gadget.repeatDirections 1152
      (bendRoutePrefixDirections firstPort secondPort
        localClauseIndex literalIndex)
  let fanWord :=
    retainedNormalizedFallbackFanSuffixDirections .ordinary
      (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData firstPort secondPort
          localClauseIndex literalIndex)) slot
  match bendRouteCardinalTangentOrientation firstPort secondPort
      localClauseIndex literalIndex with
  | .backward => sourceWord ++ fanWord
  | .forward =>
      let trim := retainedTerminalFanOuterLaneSpacing * slot.val
      sourceWord.take (sourceWord.length - trim) ++ fanWord.drop trim

/-- Translating a genuine finite bend route and then applying its ordinary
retained fan yields exactly the orientation-selected canonical normalized
word above. -/
theorem scaledSplicedOwnFigure7Route_bend_translate_normalized_directions
    (offset : Cell)
    (firstPort secondPort : CornerPort)
    (different : firstPort ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (translatePolyline offset
                (cornerEqualityRoutes firstPort secondPort
                  localClauseIndex literalIndex)))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (bendRouteTerminalData firstPort secondPort
                localClauseIndex literalIndex))
            slot)) =
      bendRouteNormalizedFallbackDirections firstPort secondPort
        localClauseIndex literalIndex slot := by
  let route := cornerEqualityRoutes firstPort secondPort
    localClauseIndex literalIndex
  let terminal := bendRouteTerminalData firstPort secondPort
    localClauseIndex literalIndex
  let data := bendRouteCardinalTangentData firstPort secondPort
    localClauseIndex literalIndex
  have certificate :=
    bendRouteCardinalTangentCertificate_of_ne firstPort secondPort
      different localClauseIndex literalIndex clauseLt literalLt
  have clearance :
      288 < retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor := by
    have cleared :=
      retainedAngularFanSourceClearanceFactor_clears_transverseBand
    omega
  cases orientationEq :
      bendRouteCardinalTangentOrientation firstPort secondPort
        localClauseIndex literalIndex with
  | backward =>
      have predecessor := certificate.predecessor slot
      rw [orientationEq] at predecessor
      simp only [BendRouteCardinalTangentOrientation.signedDistance]
        at predecessor
      have normalized :=
        scaledSplicedOwnFigure7Route_cardinalTangent_translate_normalized_directions
          offset route terminal slot data.port data.scaledLength
          data.distance retainedAngularFanSourceClearanceFactor_pos
          clearance certificate.routeLength certificate.classified
          certificate.routeSimple certificate.routeOrthogonal
          certificate.terminalLengthPositive certificate.scaledTerminalEq
          certificate.cardinal certificate.scaledLengthLarge
          certificate.distancePositive predecessor
      rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
        at normalized
      simpa [route, terminal, data,
        bendRouteNormalizedFallbackDirections, orientationEq,
        bendRoutePrefixDirections] using normalized
  | forward =>
      have predecessor := certificate.predecessor slot
      rw [orientationEq] at predecessor
      simp only [BendRouteCardinalTangentOrientation.signedDistance]
        at predecessor
      have normalized :=
        scaledSplicedOwnFigure7Route_forwardCardinalTangent_translate_normalized_directions
          offset route terminal slot data.port data.scaledLength
          data.distance retainedAngularFanSourceClearanceFactor_pos
          clearance certificate.routeLength certificate.classified
          certificate.routeSimple certificate.routeOrthogonal
          certificate.terminalLengthPositive certificate.scaledTerminalEq
          certificate.cardinal certificate.scaledLengthLarge
          (certificate.shiftStrict slot) predecessor
      rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
        at normalized
      simpa [route, terminal, data,
        bendRouteNormalizedFallbackDirections, orientationEq,
        bendRoutePrefixDirections] using normalized

end PeriodicEightOccurrenceSplit
end LeanTrominoes
