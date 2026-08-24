/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeShapeLength

/-! # Length alignment of terminal source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

@[simp] theorem terminalSourceKeyRecipeBlocks_length :
    terminalSourceKeyRecipeBlocks.length =
      carrierSegmentPredicates.length := by
  unfold terminalSourceKeyRecipeBlocks carrierSegmentPredicates
  simp

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
