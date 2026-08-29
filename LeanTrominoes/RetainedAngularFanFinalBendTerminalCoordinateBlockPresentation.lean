/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularBendTerminalCoordinateFamily
import LeanTrominoes.ListProductBoolZipIdxFlatMap

/-! # Four-incidence block presentation of final bend coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- The two implication clauses for each routed bend flatten to its canonical
four-incidence corner-table block, independently of the starting index. -/
theorem taggedBendTerminalCoordinates_eq_bendBlocks
    (bends : List RouteBend)
    (start : Nat) :
    retainedBendTaggedTerminalCoordinates bends start =
      retainedBendTerminalCoordinates bends := by
  unfold retainedBendTaggedTerminalCoordinates
  calc
    _ = bends.flatMap fun routeBend =>
        [retainedTerminalDataCoordinate
            (bendRouteTerminalDataTagged
              routeBend.incomingPort routeBend.outgoingPort true 0),
          retainedTerminalDataCoordinate
            (bendRouteTerminalDataTagged
              routeBend.incomingPort routeBend.outgoingPort true 1),
          retainedTerminalDataCoordinate
            (bendRouteTerminalDataTagged
              routeBend.incomingPort routeBend.outgoingPort false 0),
          retainedTerminalDataCoordinate
            (bendRouteTerminalDataTagged
              routeBend.incomingPort routeBend.outgoingPort false 1)] :=
      ListProductBoolZipIdxFlatMap.pair_eq_block bends start
        (fun tagged literalIndex =>
          retainedTerminalDataCoordinate
            (bendRouteTerminalDataTagged
              tagged.1.incomingPort tagged.1.outgoingPort
              tagged.2 literalIndex))
    _ = _ := by
      unfold retainedBendTerminalCoordinates
      apply List.flatMap_congr
      intro routeBend routeBendMember
      exact congrArg (List.map retainedTerminalDataCoordinate)
        (bendRouteTerminalDataTagged_block_eq
          routeBend.incomingPort routeBend.outgoingPort)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
