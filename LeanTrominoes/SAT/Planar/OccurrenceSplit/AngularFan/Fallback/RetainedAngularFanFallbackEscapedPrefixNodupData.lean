/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Common.List.ListNodupCheck
import LeanTrominoes.Computation.Encoding.Finite.FiniteBoolCheck
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictDirectionNodup
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Fallback.RetainedAngularFanFallbackEscapedRadialPrefixEndpoint
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Fallback.RetainedAngularFanFallbackExteriorRadialJoinNodup

/-! # Duplicate-freeness of escaped fallback radial prefixes -/

namespace LeanTrominoes

namespace Gadget

/-- Rebuilding a direction word commutes with translation of its start. -/
theorem rebuildRoute_add
    (offset start : Cell) (directions : List AxisDirection) :
    rebuildRoute (Cell.add offset start) directions =
      (rebuildRoute start directions).map (Cell.add offset) := by
  induction directions generalizing start with
  | nil => simp [rebuildRoute]
  | cons direction directions induction =>
      simp only [rebuildRoute, List.map_cons]
      congr 1
      rw [← induction (Cell.add start direction.step)]
      congr 1
      rcases offset with ⟨offsetX, offsetY⟩
      rcases start with ⟨startX, startY⟩
      rcases direction.step with ⟨stepX, stepY⟩
      simp [Cell.add]
      constructor <;> ring

end Gadget

namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

def escapedFixedPrefixNodupCheck (direction : RetainedTerminalDirection) : Bool :=
  finiteAll fun slot : RetainedTerminalSlot =>
    listNodupCheck (Gadget.rebuildRoute (0, 0) (prefixDirections .escaped direction slot))

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
