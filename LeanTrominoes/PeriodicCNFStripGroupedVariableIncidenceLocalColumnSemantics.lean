/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalBodyBlockSemantics

/-! # Assembling local grouped variable-incidence columns

This file packages the four aligned pieces of one grouped occurrence into an
opaque column.  The list theorem below consequently performs no reduction of
the source compiler while it replaces all global sparse body lookups.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open GroupedRoutedIncidenceKeyLocality

/-- The aligned data needed to localize one grouped variable-incidence block. -/
structure GroupedVariableIncidenceLocalColumn where
  start : Nat
  pair : GroupedVariableFanSlot
  data : FinalFanOccurrenceData
  bodyBlock : List (List AxisDirection)

namespace GroupedVariableIncidenceLocalColumn

/-- The occurrence block before global routed-key lookup is localized. -/
def globalBodyBlock
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (column : GroupedVariableIncidenceLocalColumn) :
    List (List AxisDirection) :=
  ((groupedVariableIncidencePrefixQueryBlock column.pair).zipIdx
      (3 * column.start)).map fun tagged =>
    HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
      if tagged.2 ∈ globalKeys then
        FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          globalKeys globalBodies tagged.2
      else []

/-- The same occurrence block using its three local keys and bodies. -/
def localBodyBlock
    (column : GroupedVariableIncidenceLocalColumn) :
    List (List AxisDirection) :=
  groupedVariableIncidenceLocalBodyBlock
    column.start column.pair column.data column.bodyBlock

/-- The three alignment facts that make an occurrence column localizable. -/
def Valid
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (column : GroupedVariableIncidenceLocalColumn) : Prop :=
  column.pair.1.kind (groupedVariableFanSiteSlot column.pair.2) =
      column.data.kind ∧
    (keyBlock column.start column.data).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          globalKeys globalBodies) = column.bodyBlock ∧
    ∀ query,
      column.start * 3 ≤ query →
      query <
          (column.start +
            directFinalOccurrenceTripleBlockWidth column.data) * 3 →
      (query ∈ globalKeys ↔ query ∈ keyBlock column.start column.data)

/-- A valid aligned column has identical global and local body blocks. -/
theorem globalBodyBlock_eq_localBodyBlock_of_valid
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (column : GroupedVariableIncidenceLocalColumn)
    (valid : column.Valid globalKeys globalBodies) :
    column.globalBodyBlock globalKeys globalBodies =
      column.localBodyBlock := by
  rcases valid with ⟨kindEq, bodyAligned, intervalLocal⟩
  unfold globalBodyBlock localBodyBlock
  exact groupedVariableIncidenceGlobalBodyBlock_eq_local_of_interval
    globalKeys globalBodies column.start column.pair column.data
    column.bodyBlock kindEq bodyAligned intervalLocal

/-- Pointwise-valid occurrence columns may all be localized before their
body blocks are flattened. -/
theorem flatten_map_globalBodyBlock_eq_localBodyBlock
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (columns : List GroupedVariableIncidenceLocalColumn)
    (valid : ∀ column ∈ columns, column.Valid globalKeys globalBodies) :
    (columns.map (globalBodyBlock globalKeys globalBodies)).flatten =
      (columns.map localBodyBlock).flatten := by
  apply congrArg List.flatten
  apply List.map_congr_left
  intro column columnMember
  exact globalBodyBlock_eq_localBodyBlock_of_valid
    globalKeys globalBodies column (valid column columnMember)

end GroupedVariableIncidenceLocalColumn

end LeanTrominoes.PeriodicCNFStripReduction

end
