/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData

/-! # Boolean-tagged bend terminal data -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Terminal datum selected by one direction of a bend implication. -/
def bendRouteTerminalDataTagged
    (incomingPort outgoingPort : CornerPort)
    (direction : Bool) (literalIndex : Nat) : RetainedTerminalData :=
  bendRouteTerminalData incomingPort outgoingPort
    (if direction then 0 else 1) literalIndex

/-- Scanning both tagged implications in clause-major order gives the
canonical four-incidence bend terminal block. -/
theorem bendRouteTerminalDataTagged_block_eq
    (incomingPort outgoingPort : CornerPort) :
    [bendRouteTerminalDataTagged incomingPort outgoingPort true 0,
      bendRouteTerminalDataTagged incomingPort outgoingPort true 1,
      bendRouteTerminalDataTagged incomingPort outgoingPort false 0,
      bendRouteTerminalDataTagged incomingPort outgoingPort false 1] =
      bendRouteTerminalDataBlock incomingPort outgoingPort := by
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
