/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.PlanarThreeDMVariableSiteDrawing

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

noncomputable instance : Primcodable VariableSiteSlot :=
  Primcodable.ofEquiv (Fin (Fintype.card VariableSiteSlot))
    (Fintype.equivFin VariableSiteSlot)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
