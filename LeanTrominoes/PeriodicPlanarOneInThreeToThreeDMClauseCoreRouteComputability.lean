/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PlanarX3CClauseDrawing
import LeanTrominoes.OrthogonalDrawing

/-! # Computability of finite clause-core routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The complete local clause-core route family is a fixed finite table. -/
theorem x3cClauseOrthogonalRoute_primrec :
    Primrec
      (fun input : X3CClauseSet × WireColor =>
        X3CClauseOrthogonal.route input.1 input.2) :=
  Computability.finiteDomain_primrec _

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
