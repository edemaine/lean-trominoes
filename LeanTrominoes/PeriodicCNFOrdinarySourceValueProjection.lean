/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceSelectedValues
import LeanTrominoes.FiniteTemplateQuerySemantics
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Projection of complete inherited columns to ordinary literal rows -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation PeriodicCNFStripReduction
open HorizontalRoutedRouteHeaderPresentationAtomScope

abbrev ValueBlock := DirectedClauseProfile × SourceOccurrenceAtomValueRow

def valueBlock (block : ValueBlock) : List Nat := (clauseBlock block.1).map block.2.value

def orderedValues (profile : DirectedClauseProfile) (values : List Nat) : List Nat :=
  (slots profile).map (fun slot => values.getD (sourceSlotNat (presentationSlotAt profile slot)) 0)

theorem valueBlock_length (block : ValueBlock) :
    (valueBlock block).length = tokenSize (.clause block.1) := by
  simp only [valueBlock, clauseBlock, List.length_map, tokenSize]

theorem valueBlock_offsets_valid (block : ValueBlock) (i : Nat)
    (member : i ∈ tokenOffsets (.clause block.1)) : i < (valueBlock block).length := by
  change i ∈ (slots block.1).map (selectedIndex block.1) at member
  obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
  rw [valueBlock_length]
  exact selectedIndex_lt block.1 slot ((slots_active _ _).1 slotMember)

theorem queryValues (blocks : List ValueBlock) :
    (queries (blocks.map (fun block => Token.clause block.1))).map
      (fun i => (blocks.flatMap valueBlock).getD i 0) =
      blocks.flatMap (fun block => orderedValues block.1 block.2.literals) := by
  rw [queries, FiniteTemplateQueries.lookup_payload _ _ _ valueBlock blocks
    (fun block _ => valueBlock_length block) valueBlock_offsets_valid 0]
  apply List.flatMap_congr
  intro block _
  simp only [tokenOffsets, List.map_map, orderedValues, Function.comp_def]
  apply List.map_congr_left
  intro slot member
  exact selectedValue block.1 slot ((slots_active _ _).1 member) block.2

theorem queryValid (blocks : List ValueBlock) (i : Nat)
    (member : i ∈ queries (blocks.map (fun block => Token.clause block.1))) :
    i < (blocks.flatMap valueBlock).length := by
  have valid : ∀ token j, j ∈ tokenOffsets token → j < tokenSize token := by
    intro token j member
    cases token with
    | «variable» => simp [tokenOffsets] at member
    | clause profile =>
      change j ∈ (slots profile).map (selectedIndex profile) at member
      obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
      exact selectedIndex_lt profile slot ((slots_active _ _).1 slotMember)
  have bound := (FiniteTemplateQueries.queriesFrom_bound tokenSize tokenOffsets valid _ 0 i member).2
  simpa only [List.map_map, Function.comp_def, List.length_flatMap, valueBlock_length, Nat.zero_add] using bound

theorem lookupValues (blocks : List ValueBlock) :
    UnaryIndexedValueLookup.values (queries (blocks.map (fun block => Token.clause block.1)))
      (blocks.flatMap valueBlock) =
      blocks.flatMap (fun block => orderedValues block.1 block.2.literals) := by
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (queryValid blocks)]
  exact queryValues blocks

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
