/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataCode

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem variableRibbonFanDataToCode_ofCode
    (data : VariableRibbonFanCode) :
    variableRibbonFanDataToCode (variableRibbonFanDataOfCode data) = data := by
  rcases data with ⟨countPred, ⟨⟨firstKind, secondKind,
    thirdKind⟩, ⟨⟨firstPolarity, secondPolarity, thirdPolarity⟩,
    ⟨firstDirection, secondDirection, thirdDirection⟩⟩⟩⟩
  simp [variableRibbonFanDataOfCode, variableRibbonFanDataToCode]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
