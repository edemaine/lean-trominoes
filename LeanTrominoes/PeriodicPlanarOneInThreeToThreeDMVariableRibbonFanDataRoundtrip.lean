/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataCode

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem variableRibbonFanDataOfCode_toCode
    (data : VariableRibbonFanData) :
    variableRibbonFanDataOfCode (variableRibbonFanDataToCode data) = data := by
  cases data with
  | mk countPred kind polarity direction =>
      unfold variableRibbonFanDataOfCode variableRibbonFanDataToCode
      congr 1
      · funext slot; cases slot <;> simp
      · funext slot; cases slot <;> rfl
      · funext slot; cases slot <;> simp

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
