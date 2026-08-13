/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCommonFrameBoundaries
import LeanTrominoes.RetainedTerminalBoundaryCheckpointSeparation

/-!
# Common-frame carrier boundaries as terminal corridors

An arbitrary final carrier boundary already contains the two pointwise
half-plane bounds needed by the refined terminal-checkpoint argument.  This
small adapter keeps projection of those dependent fields out of the much
larger relative source-corridor reduction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A carrier boundary for two arbitrary final route occurrences, together
with strict prefix avoidance, supplies the refined source corridor. -/
theorem
    FinalGaugedFlatNormalizedCarrierBoundary.sourcePrefixCorridorSeparated
    {carrierRoute macrocellRoute : List Cell}
    (boundary :
      FinalGaugedFlatNormalizedCarrierBoundary
        carrierRoute macrocellRoute)
    (terminal : RetainedTerminalData)
    (macrocellLength : 2 ≤ macrocellRoute.length)
    (macrocellClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector macrocellRoute) = some terminal)
    (strictlyAvoid :
      RoutesStrictlyAvoidEachOther
        carrierRoute.dropLast macrocellRoute) :
    SourcePrefixCorridorSeparated
      carrierRoute macrocellRoute terminal.1 := by
  apply
    sourcePrefixCorridorSeparated_of_outside_insideCarrierBoundary
      boundary.port boundary.origin carrierRoute macrocellRoute terminal
      macrocellLength macrocellClassified
  · intro point pointMember
    exact boundary.carrierOutside point
      (List.mem_of_mem_dropLast pointMember)
  · exact boundary.macrocellInside
  · exact strictlyAvoid

end PeriodicOrthocrossing
end LeanTrominoes
