/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineExtendedRouteDecomposition

/-!
# Finite compiler for normalized Figure 9 extended connectors

The extended connector depends only on finite fan metadata and one of three
slots.  Its loop-erased direction word is therefore a fixed finite block,
and translation into an arbitrary clause gauge does not change that block.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Computability Turing
open Gadget PeriodicOrthocrossing

/-- Finite input selecting one extended connector direction block. -/
structure ExtendedDirectionQuery where
  data : ComposedClauseExitFanData
  slot : Fin 3
  deriving DecidableEq, Fintype

/-- The complete loop-erased direction word of one unshifted finite
extended connector. -/
def normalizedExtendedDirectionBlock
    (query : ExtendedDirectionQuery) : List AxisDirection :=
  unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      (query.data.extendedRoute query.slot))

/-- Moving an active extended connector into a clause gauge preserves its
finite normalized direction block. -/
theorem normalizedTranslatedExtendedRoute_directionWord
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (data.translatedExtendedRoute origin slot)) =
      normalizedExtendedDirectionBlock ⟨data, slot⟩ := by
  have extendedNonempty : data.extendedRoute slot ≠ [] := by
    intro empty
    have head := data.extendedRoute_head? valid slot active
    simp [empty] at head
  have extendedOrthogonal :
      OrthogonalPolyline (data.extendedRoute slot) :=
    data.extendedRoute_orthogonal valid slot active
  unfold ComposedClauseExitFanData.translatedExtendedRoute
    translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    extendedNonempty extendedOrthogonal origin]
  change unitSubdivisionDirections
      (translatePolyline origin
        (AxisDirection.normalizeOrthogonalPolyline
          (data.extendedRoute slot))) = _
  rw [unitSubdivisionDirections_translatePolyline]
  rfl

local instance extendedDirectionAxisDirectionInhabited :
    Inhabited AxisDirection := ⟨.invalid⟩

/-- A fixed finite block transducer emits all selected normalized extended
connector words in linear time. -/
noncomputable def normalizedExtendedDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ExtendedDirectionQuery)
      (List AxisDirection)
      ExtendedDirectionQuery AxisDirection
      id id
      (fun queries => queries.flatMap normalizedExtendedDirectionBlock) :=
  FiniteBlockTransducer.computableInPolyTime
    normalizedExtendedDirectionBlock

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

end
