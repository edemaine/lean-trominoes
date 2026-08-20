/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteSlotEncoding

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

noncomputable instance : Primcodable VariableSiteTriple :=
  Primcodable.ofEquiv (Fin (Fintype.card VariableSiteTriple))
    (Fintype.equivFin VariableSiteTriple)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
