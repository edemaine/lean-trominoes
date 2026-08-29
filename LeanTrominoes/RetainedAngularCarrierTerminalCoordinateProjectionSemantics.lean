/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateData
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions

/-! # Projections of retained carrier terminal coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open TerminalCoordinateComponents

/-- The direction projection of mapped compiled terminal data is exactly
the retained carrier direction-rank column. -/
theorem carrierTerminalCoordinates_directionRanks
    (descriptors : List RouteDescriptor) :
    directionRanks
        (List.map retainedTerminalDataCoordinate
          (CarrierRankOrderedPairs.retainedTerminalDataBlocks
            descriptors).flatten) =
      CarrierRankOrderedPairs.retainedTerminalDirectionRanks
        descriptors := by
  unfold directionRanks retainedTerminalDataCoordinate
    CarrierRankOrderedPairs.retainedTerminalDirectionRanks
    terminalDataDirectionRanks
  simp [List.map_map, Function.comp_def]

/-- The radial projection of mapped compiled terminal data is exactly the
retained carrier radial-length column. -/
theorem carrierTerminalCoordinates_radialLengths
    (descriptors : List RouteDescriptor) :
    radialLengths
        (List.map retainedTerminalDataCoordinate
          (CarrierRankOrderedPairs.retainedTerminalDataBlocks
            descriptors).flatten) =
      CarrierRankOrderedPairs.retainedTerminalRadialLengths
        descriptors := by
  unfold radialLengths retainedTerminalDataCoordinate
    CarrierRankOrderedPairs.retainedTerminalRadialLengths
    terminalDataRadialLengths
  simp [List.map_map, Function.comp_def]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
