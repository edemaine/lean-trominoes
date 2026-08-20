/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped
import Mathlib.Data.List.Basic

/-! # Variable-width occurrence blocks in the planar 3DM triple list -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Stable variable/slot order underlying the variable-module triple prefix. -/
def usedOccurrenceSlots {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Variable × OccurrenceSlot) :=
  (occurringVariables source).flatMap fun atom =>
    (usedSlots source atom).map fun slot => (atom, slot)

/-- Triple block contributed by one used occurrence slot. -/
def occurrenceTripleBlock {Variable Position : Type*}
    [DecidableEq Variable]
    (source : PeriodicCNF Variable) (position : Triple Variable → Position)
    (entry : Variable × OccurrenceSlot) : List Position :=
  (occurrenceTriples source entry.1 entry.2).map position

/-- Width of one connector block: seven for the fixed-red detour and three
for either ordinary connector. -/
def occurrenceTripleBlockWidth {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot) : Nat :=
  match occurrenceConnectorKind source entry.1 entry.2 with
  | .fixedRed => 7
  | .fixedGreen | .fixedBlue => 3

@[simp] theorem occurrenceTripleBlock_length
    {Variable Position : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (position : Triple Variable → Position)
    (entry : Variable × OccurrenceSlot) :
    (occurrenceTripleBlock source position entry).length =
      occurrenceTripleBlockWidth source entry := by
  unfold occurrenceTripleBlock occurrenceTripleBlockWidth
    occurrenceTriples
  cases occurrenceConnectorKind source entry.1 entry.2 <;>
    simp [allFixedRedTriples, allOrdinaryTriples]

/-- Mapping any pointwise triple datum over the variable prefix is exactly a
scan of the stable used-slot list by its connector blocks. -/
theorem variableTriples_map_eq_occurrenceBlocks
    {Variable Position : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (position : Triple Variable → Position) :
    (variableTriples source).map position =
      (usedOccurrenceSlots source).flatMap
        (occurrenceTripleBlock source position) := by
  unfold variableTriples usedOccurrenceSlots occurrenceTripleBlock
  simp only [List.map_flatMap, List.flatMap_assoc,
    List.flatMap_map]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
