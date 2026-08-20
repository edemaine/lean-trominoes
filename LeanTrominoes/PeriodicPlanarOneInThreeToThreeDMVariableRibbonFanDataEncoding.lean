/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataEquivalence

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

noncomputable instance : Primcodable VariableRibbonFanData :=
  Primcodable.ofEquiv _ variableRibbonFanDataEquivData

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
