/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActivitySemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceFiniteDirectionData

/-! # Compact direction blocks for horizontal variable incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A variable incidence is either one finite local table route, or that
finite prefix extended by a compact coordinated occurrence route. -/
inductive HorizontalVariableTypedIncidenceDirectionBlock where
  | local
  | routed (occurrence : HorizontalRoutedRouteDirectionBlock)

/-- Interpret one variable-incidence block at its proof-free table query. -/
def horizontalVariableTypedIncidenceDirections
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    HorizontalVariableTypedIncidenceDirectionBlock → List AxisDirection
  | .local =>
      horizontalVariableIncidencePrefixDirections
        (horizontalVariableRoutePrefixQueryComputed input)
  | .routed occurrence =>
      horizontalVariableIncidencePrefixDirections
          (horizontalVariableRoutePrefixQueryComputed input) ++
        horizontalOccurrenceCoordinatedDirections
          (horizontalVariableOccurrenceRouteQueryComputed input)
          occurrence

/-- Every active source slot produces a successful proof-free horizontal
occurrence lookup. -/
theorem exists_horizontalOccurrenceLookupComputed_of_slot_mem
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : OccurrenceSlot)
    (slotMember : slot ∈ usedSlots
      (horizontalSemanticNormalizedRibbonSource source).erase atom) :
    ∃ tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable,
      horizontalOccurrenceLookupComputed ((source, atom), slot) =
        some tagged := by
  have semanticSome :
      (occurrenceAt
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).isSome = true :=
    (occurrenceAt_isSome_eq_true_iff_mem_usedSlots
      (horizontalSemanticNormalizedRibbonSource source).erase
      atom slot).mpr slotMember
  rcases Option.isSome_iff_exists.mp semanticSome with
    ⟨tagged, semanticLookup⟩
  refine ⟨tagged, ?_⟩
  unfold horizontalOccurrenceLookupComputed
    horizontalOccurrenceLookupInput
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
  exact semanticLookup

end PeriodicCNFStripReduction
end LeanTrominoes

end
