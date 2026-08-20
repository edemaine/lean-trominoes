/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataRoundtrip
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanCodeRoundtrip

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

def variableRibbonFanDataEquivData :
    VariableRibbonFanData ≃ VariableRibbonFanCode where
  toFun := variableRibbonFanDataToCode
  invFun := variableRibbonFanDataOfCode
  left_inv := variableRibbonFanDataOfCode_toCode
  right_inv := variableRibbonFanDataToCode_ofCode

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
