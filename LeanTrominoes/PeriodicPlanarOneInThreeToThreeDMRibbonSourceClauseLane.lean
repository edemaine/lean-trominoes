/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans

/-! # Source clause-terminal ribbon lanes -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The physical lane selected by a source occurrence is the standard lane
permutation advertised by its clause terminal group. -/
theorem routedRibbonLane_eq_clauseTerminalGroup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    routedRibbonLane source entry color =
      clauseRibbonLaneForColor
        (occurrenceClauseTerminalGroup source entry) color := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
