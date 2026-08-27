/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationThreeRoundDirections
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time three-round direction normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM

open Computability Turing

/-- With the six endpoint templates fixed in the finite program, all three
normalization rounds are one polynomial-time direction-word transduction. -/
noncomputable def
    threeRoundNormalizationDirectionsFromUnitDirectionsComputableInPolyTime
    (firstSourceTemplate firstTargetTemplate : List Cell)
    (secondSourceTemplate secondTargetTemplate : List Cell)
    (finalSourceTemplate finalTargetTemplate : List Cell) :
    TM2ComputableInPolyTime id id
      (threeRoundNormalizationDirectionsFromUnitDirections
        firstSourceTemplate firstTargetTemplate
        secondSourceTemplate secondTargetTemplate
        finalSourceTemplate finalTargetTemplate) := by
  let first := normalizationDirectionWordComputableInPolyTime
    firstSourceTemplate firstTargetTemplate
  let second := TM2CompositionMachine.computableInPolyTime first
    (normalizationDirectionWordComputableInPolyTime
      secondSourceTemplate secondTargetTemplate)
  let final := TM2CompositionMachine.computableInPolyTime second
    (normalizationDirectionWordComputableInPolyTime
      finalSourceTemplate finalTargetTemplate)
  change TM2ComputableInPolyTime id id
    (fun oldDirections =>
      normalizationDirectionWord finalSourceTemplate finalTargetTemplate
        (normalizationDirectionWord
          secondSourceTemplate secondTargetTemplate
          (normalizationDirectionWord
            firstSourceTemplate firstTargetTemplate oldDirections)))
  exact final

end PeriodicThreeDM
end LeanTrominoes

end
