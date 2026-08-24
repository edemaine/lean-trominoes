/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipeData

/-! # Route-shape length alignment of terminal source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

@[simp] theorem RouteShape.terminalSourceKeyRecipeBlocks_length
    (shape : RouteShape) :
    shape.terminalSourceKeyRecipeBlocks.length =
      shape.carrierSegmentPredicates.length := by
  unfold RouteShape.terminalSourceKeyRecipeBlocks
    RouteShape.carrierSegmentPredicates
  simp [Segment.terminalSourceKeyRecipeBlocks,
    Segment.carrierAxisPredicates]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
