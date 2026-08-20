/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseOuterFans

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

noncomputable instance : Primcodable ClauseRibbonFanData :=
  Primcodable.ofEquiv (Fin (Fintype.card ClauseRibbonFanData))
    (Fintype.equivFin ClauseRibbonFanData)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
