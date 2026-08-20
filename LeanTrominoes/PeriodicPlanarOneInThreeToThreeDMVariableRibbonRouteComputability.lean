/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataEncoding
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteSlotEncoding
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans
import LeanTrominoes.OrthogonalDrawing

/-! # Computability of the finite variable-side ribbon routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The complete variable-side endpoint fan is a fixed finite lookup table.
Packaging all of its inputs together lets later source-level computations use
the table without unfolding its large geometric case split. -/
theorem variableRibbonCoordinatedRoute_primrec :
    Primrec
      (fun input :
          VariableRibbonFanData × (VariableSiteSlot × WireColor) =>
        input.1.coordinatedRoute input.2.1 input.2.2) :=
  Computability.finiteDomain_primrec _

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
