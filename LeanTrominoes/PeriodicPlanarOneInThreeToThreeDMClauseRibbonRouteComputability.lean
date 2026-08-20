/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseRibbonFanDataEncoding
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans
import LeanTrominoes.OrthogonalDrawing

/-! # Computability of the finite clause-side ribbon routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The complete clause-side endpoint fan is a fixed finite lookup table. -/
theorem clauseRibbonCoordinatedRoute_primrec :
    Primrec
      (fun input :
          ClauseRibbonFanData × (X3CClauseTerminalGroup × WireColor) =>
        input.1.coordinatedRoute input.2.1 input.2.2) :=
  Computability.finiteDomain_primrec _

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
