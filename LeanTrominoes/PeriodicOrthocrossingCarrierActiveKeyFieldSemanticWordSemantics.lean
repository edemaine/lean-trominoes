/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeySemanticWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData

/-! # Generic semantic words of the active carrier-key stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every compiled active carrier-key word is also the generic field
projector's canonical word for its aligned optional physical key. -/
theorem CarrierActiveKeyRecipeStream.guardedWords_eq_keyFieldSemanticWords
    (descriptors : List RouteDescriptor) :
    CarrierActiveKeyRecipeStream.guardedWords descriptors =
      (CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
        CarrierKeyFieldProjector.semanticWord := by
  rw [CarrierActiveKeyRecipeStream.guardedWords_eq_semanticWords]
  apply List.map_congr_left
  intro key _keyMember
  cases key <;> rfl

end LeanTrominoes.PeriodicOrthocrossing

end
