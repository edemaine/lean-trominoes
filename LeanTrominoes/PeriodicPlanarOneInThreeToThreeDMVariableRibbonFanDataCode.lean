/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableConnectorKindEquivalence
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMAxisDirectionEquivalence
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanFinite

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

abbrev VariableRibbonFanCode :=
  Fin 3 ×
    ((Fin 3 × Fin 3 × Fin 3) ×
      ((Bool × Bool × Bool) ×
        (Fin 5 × Fin 5 × Fin 5)))

def variableRibbonFanDataToCode
    (data : VariableRibbonFanData) : VariableRibbonFanCode :=
  (data.countPred,
    ((variableConnectorKindEquivFin (data.kind .first),
        variableConnectorKindEquivFin (data.kind .second),
        variableConnectorKindEquivFin (data.kind .third)),
      ((data.polarity .first, data.polarity .second,
          data.polarity .third),
        (axisDirectionEquivFin (data.direction .first),
          axisDirectionEquivFin (data.direction .second),
          axisDirectionEquivFin (data.direction .third)))))

def variableRibbonFanDataOfCode
    (data : VariableRibbonFanCode) : VariableRibbonFanData :=
  { countPred := data.1
    kind := fun slot => match slot with
      | .first => variableConnectorKindEquivFin.symm data.2.1.1
      | .second => variableConnectorKindEquivFin.symm data.2.1.2.1
      | .third => variableConnectorKindEquivFin.symm data.2.1.2.2
    polarity := fun slot => match slot with
      | .first => data.2.2.1.1
      | .second => data.2.2.1.2.1
      | .third => data.2.2.1.2.2
    direction := fun slot => match slot with
      | .first => axisDirectionEquivFin.symm data.2.2.2.1
      | .second => axisDirectionEquivFin.symm data.2.2.2.2.1
      | .third => axisDirectionEquivFin.symm data.2.2.2.2.2 }

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
