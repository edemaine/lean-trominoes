/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalBodyBlockSemantics

/-! # Source specialization of local grouped variable-incidence bodies -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open GroupedRoutedIncidenceKeyLocality

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The globally keyed complete body block presented at one grouped
occurrence index. -/
def directSourceFinalGroupedVariableIncidenceGlobalBodyBlockAt
    (symbols : List encoding.Γ) (index : Nat)
    (pair : GroupedVariableFanSlot) : List (List AxisDirection) :=
  ((groupedVariableIncidencePrefixQueryBlock pair).zipIdx
      (3 * directSourceFinalGroupedOccurrenceTripleBlockStartAt
        decider symbols index)).map fun tagged =>
    HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
      if tagged.2 ∈
          directSourceFinalGroupedRoutedIncidenceKeys decider symbols then
        FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
          (directSourceFinalGroupedColoredOccurrenceDirectionBodies
            decider symbols)
          tagged.2
      else []

/-- The equivalent occurrence-local three-key/three-body presentation. -/
def directSourceFinalGroupedVariableIncidenceLocalBodyBlockAt
    (symbols : List encoding.Γ) (index : Nat)
    (pair : GroupedVariableFanSlot)
    (bodyBlock : List (List AxisDirection)) : List (List AxisDirection) :=
  groupedVariableIncidenceLocalBodyBlock
    (directSourceFinalGroupedOccurrenceTripleBlockStartAt
      decider symbols index)
    pair
    (directSourceFinalGroupedOccurrenceDataAt decider symbols index)
    bodyBlock

/-- Equal connector kinds identify one in-range occurrence interval, after
which global routed-key membership and body lookup both reduce to that
occurrence's local data. -/
theorem directSourceFinalGroupedVariableIncidenceBodyBlock_eq_local
    (symbols : List encoding.Γ) (index : Nat)
    (pair : GroupedVariableFanSlot)
    (bodyBlock : List (List AxisDirection))
    (indexLt : index <
      (directSourceFinalGroupedOccurrenceData decider symbols).length)
    (kindEq :
      pair.1.kind (groupedVariableFanSiteSlot pair.2) =
        (directSourceFinalGroupedOccurrenceDataAt
          decider symbols index).kind)
    (bodyAligned :
      (keyBlock
          (directSourceFinalGroupedOccurrenceTripleBlockStartAt
            decider symbols index)
          (directSourceFinalGroupedOccurrenceDataAt
            decider symbols index)).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
          (directSourceFinalGroupedColoredOccurrenceDirectionBodies
            decider symbols)) = bodyBlock) :
    directSourceFinalGroupedVariableIncidenceGlobalBodyBlockAt
        decider symbols index pair =
      directSourceFinalGroupedVariableIncidenceLocalBodyBlockAt
        decider symbols index pair bodyBlock := by
  unfold directSourceFinalGroupedVariableIncidenceGlobalBodyBlockAt
    directSourceFinalGroupedVariableIncidenceLocalBodyBlockAt
  apply groupedVariableIncidenceGlobalBodyBlock_eq_local_of_interval
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies
      decider symbols)
    (directSourceFinalGroupedOccurrenceTripleBlockStartAt
      decider symbols index)
    pair
    (directSourceFinalGroupedOccurrenceDataAt decider symbols index)
    bodyBlock kindEq bodyAligned
  intro query lower upper
  exact directSourceFinalGroupedRoutedIncidenceKey_mem_iff_local
    decider symbols index query indexLt lower upper

end LeanTrominoes.PeriodicCNFStripReduction

end
