/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.RetainedAngularFanFallbackCardinalTangentNormalizedDirections
import LeanTrominoes.RetainedAngularFanSourceSpliceTranslation

/-! # Translation of cardinal-tangent normalized fallbacks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

set_option maxRecDepth 10000

/-- Translating the raw source route does not change the normalized direction
word supplied by the cardinal-tangent fallback theorem. -/
theorem scaledSplicedOwnFigure7Route_cardinalTangent_translate_normalized_directions
    {factor : Nat}
    (offset : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (port : Port)
    (scaledLength distance : Nat)
    (factorPositive : 0 < factor)
    (clearance :
      288 < retainedTerminalFanTotalRefinement * factor)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeSimple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (scaledTerminalEq :
      scaleRetainedTerminalData factor terminal =
        (.compass port, scaledLength))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (scaledLengthLarge : 2 ≤ scaledLength)
    (distancePositive : 0 < distance)
    (predecessor :
      (retainedFallbackSourcePrefix
        (scalePolyline factor route)).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter
                (scalePolyline factor route))
              (.compass port, scaledLength) slot).gate
            (Cell.scale (-(distance : Int))
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline factor
              (translatePolyline offset route))
            (scaleRetainedTerminalData factor terminal) slot)) =
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route)) ++
        retainedNormalizedFallbackFanSuffixDirections
          .ordinary (scaleRetainedTerminalData factor terminal) slot := by
  let baseScaled := scalePolyline factor route
  let translatedRoute := translatePolyline offset route
  let translatedScaled := scalePolyline factor translatedRoute
  let scaledOffset := Cell.scale
    (retainedTerminalFanTotalRefinement * factor) offset
  let basePrefix := retainedFallbackSourcePrefix baseScaled
  let translatedPrefix := retainedFallbackSourcePrefix translatedScaled
  let baseCenter := retainedFallbackFanCenter baseScaled
  let translatedCenter := retainedFallbackFanCenter translatedScaled
  let baseGate :=
    (retainedAngularFanOuterDemand baseCenter
      (.compass port, scaledLength) slot).gate
  let translatedGate :=
    (retainedAngularFanOuterDemand translatedCenter
      (.compass port, scaledLength) slot).gate
  have baseScaledNonempty : baseScaled ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa [baseScaled, scalePolyline] using
      (show 0 < route.length by omega)
  have translatedScaledEq :
      translatedScaled =
        translatePolyline (Cell.scale factor offset) baseScaled := by
    simpa [translatedScaled, translatedRoute, baseScaled] using
      scalePolyline_translatePolyline' factor offset route
  have translatedPrefixEq :
      translatedPrefix = translatePolyline scaledOffset basePrefix := by
    calc
      translatedPrefix =
          (scalePolyline retainedTerminalFanTotalRefinement
            (translatePolyline (Cell.scale factor offset)
              baseScaled)).dropLast := by
        simp only [translatedPrefix, retainedFallbackSourcePrefix,
          translatedScaledEq]
      _ =
          (translatePolyline
            (Cell.scale retainedTerminalFanTotalRefinement
              (Cell.scale factor offset))
            (scalePolyline retainedTerminalFanTotalRefinement
              baseScaled)).dropLast := by
        rw [scalePolyline_translatePolyline']
      _ = translatePolyline
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale factor offset))
          (scalePolyline retainedTerminalFanTotalRefinement
            baseScaled).dropLast := by
        simp [translatePolyline, List.map_dropLast]
      _ = translatePolyline scaledOffset basePrefix := by
        simp [scaledOffset, basePrefix, retainedFallbackSourcePrefix,
          Cell.scale_scale]
  have translatedCenterEq :
      translatedCenter = Cell.add scaledOffset baseCenter := by
    dsimp only [translatedCenter, retainedFallbackFanCenter]
    rw [translatedScaledEq,
      translatePolyline_getLastD
        (Cell.scale factor offset) baseScaled baseScaledNonempty]
    simp [scaledOffset, baseCenter, retainedFallbackFanCenter,
      Cell.scale_add, Cell.scale_scale]
  have translatedGateEq :
      translatedGate = Cell.add scaledOffset baseGate := by
    dsimp only [translatedGate, baseGate]
    rw [translatedCenterEq]
    unfold retainedAngularFanOuterDemand retainedTerminalSplicePoint
    rcases scaledOffset with ⟨offsetX, offsetY⟩
    rcases baseCenter with ⟨centerX, centerY⟩
    rcases
        (scaleRetainedTerminalData retainedTerminalFanTotalRefinement
          (.compass port, scaledLength)).1.primitive with
      ⟨stepX, stepY⟩
    simp [Cell.add, Cell.scale]
    constructor <;> ring
  have translatedPredecessor :
      translatedPrefix.dropLast.getLast? =
        some
          (Cell.add translatedGate
            (Cell.scale (-(distance : Int))
              (retainedTerminalFanOuterLaneStep
                (.compass port)))) := by
    have basePredecessor :
        basePrefix.dropLast.getLast? =
          some
            (Cell.add baseGate
              (Cell.scale (-(distance : Int))
                (retainedTerminalFanOuterLaneStep
                  (.compass port)))) := by
      simpa [basePrefix, baseScaled, baseCenter, baseGate] using predecessor
    rw [translatedPrefixEq]
    unfold translatePolyline
    rw [← List.map_dropLast, List.getLast?_map, basePredecessor]
    simp only [Option.map_some, translatedGateEq]
    rcases scaledOffset with ⟨offsetX, offsetY⟩
    rcases baseGate with ⟨gateX, gateY⟩
    rcases retainedTerminalFanOuterLaneStep (.compass port) with
      ⟨stepX, stepY⟩
    simp [Cell.add, Cell.scale]
    constructor <;> ring
  have translatedLength : 3 ≤ translatedRoute.length := by
    simpa [translatedRoute, translatePolyline] using routeLength
  have translatedClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector translatedRoute) =
        some terminal := by
    simpa [translatedRoute, routeTerminalVector_translatePolyline] using
      classified
  have translatedSimple :
      LocalIncidenceDrawing.RouteIsSimple translatedRoute := by
    simpa [translatedRoute, translatePolyline] using
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        routeSimple offset
  have translatedOrthogonal : OrthogonalPolyline translatedRoute := by
    simpa [translatedRoute] using routeOrthogonal.translate offset
  have normalized :=
    scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
      translatedRoute terminal slot port scaledLength distance
      factorPositive clearance translatedLength translatedClassified
      translatedSimple translatedOrthogonal terminalLengthPositive
      scaledTerminalEq cardinal scaledLengthLarge distancePositive
      (by simpa [translatedScaled, translatedPrefix, translatedCenter,
        translatedGate] using translatedPredecessor)
  rw [show retainedFallbackSourcePrefix
      (scalePolyline factor translatedRoute) = translatedPrefix by
        rfl,
    translatedPrefixEq,
    Gadget.unitSubdivisionDirections_translatePolyline] at normalized
  simpa [translatedRoute, baseScaled, basePrefix] using normalized

end PeriodicEightOccurrenceSplit
end LeanTrominoes
