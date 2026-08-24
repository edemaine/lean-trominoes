/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Routed-variable cycle blocks indexed by target vertex -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Deterministically find the occurrence-prefix descriptor at a target
vertex index. -/
def occurrenceRouteDescriptorAtTargetIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (targetIndex : Nat) :
    Option RouteDescriptor :=
  (occurrenceRouteDescriptors source).find? fun descriptor =>
    decide (descriptor.targetVertexIndex = targetIndex)

/-- The current- or next-slice cycle block determined by the source
occurrence at one rotated target vertex. -/
def routedVariableCycleBlockAtTargetIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (targetIndex : Nat) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  match occurrenceRouteDescriptorAtTargetIndex source targetIndex with
  | some descriptor =>
      (if descriptor.offset = ((0, 0) : Cell) then
          routedVariableCurrentCycleBlock else []) ++
        (if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextCycleBlock else [])
  | none => []

end PeriodicThreeSATThree
end LeanTrominoes
