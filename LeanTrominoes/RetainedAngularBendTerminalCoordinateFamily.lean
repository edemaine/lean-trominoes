/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTaggedBendTerminalData
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateData

/-! # Tagged and block presentations of retained bend coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Two coordinates per tagged bend implication; global clause indices are
retained by the scan even though terminal data itself does not use them. -/
def retainedBendTaggedTerminalCoordinates
    (bends : List RouteBend)
    (start : Nat) : List (Nat × Nat) :=
  (((bends.product [true, false]).zipIdx start).flatMap fun tagged =>
    [retainedTerminalDataCoordinate
        (bendRouteTerminalDataTagged
          tagged.1.1.incomingPort tagged.1.1.outgoingPort
          tagged.1.2 0),
      retainedTerminalDataCoordinate
        (bendRouteTerminalDataTagged
          tagged.1.1.incomingPort tagged.1.1.outgoingPort
          tagged.1.2 1)])

/-- One canonical four-coordinate terminal block per routed bend. -/
def retainedBendTerminalCoordinates
    (bends : List RouteBend) : List (Nat × Nat) :=
  bends.flatMap fun routeBend =>
    List.map retainedTerminalDataCoordinate
      (bendRouteTerminalDataBlock
        routeBend.incomingPort routeBend.outgoingPort)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
