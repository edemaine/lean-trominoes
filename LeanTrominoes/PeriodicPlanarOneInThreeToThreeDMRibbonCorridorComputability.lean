/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorFoldComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorCorrectness

/-! # Computability of the ribbon corridor assembler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- The reusable macrocell ribbon-corridor assembler is primitive recursive. -/
theorem ribbonCorridorCore_primrec :
    Primrec fun input : WireColor × List Cell =>
      ribbonCorridorCore input.1 input.2 :=
  ribbonCorridorCoreComputed_primrec.of_eq fun input =>
    ribbonCorridorCoreComputed_eq input.1 input.2

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
