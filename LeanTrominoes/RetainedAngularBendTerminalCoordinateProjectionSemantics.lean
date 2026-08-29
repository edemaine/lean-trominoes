/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularBendTerminalCoordinateFamily
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Projections of retained bend terminal coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open TerminalCoordinateComponents

/-- The direction projection of canonical bend-coordinate blocks is exactly
the flattened corner-table direction-rank stream. -/
theorem bendTerminalCoordinates_directionRanks
    (bends : List RouteBend) :
    directionRanks (retainedBendTerminalCoordinates bends) =
      bends.flatMap fun routeBend =>
        terminalDataDirectionRanks
          (bendRouteTerminalDataBlock
            routeBend.incomingPort routeBend.outgoingPort) := by
  unfold directionRanks retainedBendTerminalCoordinates
    retainedTerminalDataCoordinate terminalDataDirectionRanks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro routeBend routeBendMember
  simp [List.map_map, Function.comp_def]

/-- The radial projection of canonical bend-coordinate blocks is exactly the
flattened corner-table radial-length stream. -/
theorem bendTerminalCoordinates_radialLengths
    (bends : List RouteBend) :
    radialLengths (retainedBendTerminalCoordinates bends) =
      bends.flatMap fun routeBend =>
        terminalDataRadialLengths
          (bendRouteTerminalDataBlock
            routeBend.incomingPort routeBend.outgoingPort) := by
  unfold radialLengths retainedBendTerminalCoordinates
    retainedTerminalDataCoordinate terminalDataRadialLengths
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro routeBend routeBendMember
  simp [List.map_map, Function.comp_def]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
