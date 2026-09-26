/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceQueries
import LeanTrominoes.FiniteTemplateQuerySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs

/-! # Ordinary route queries select matching header and tail pairs -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNinePolarityRouteTail ClauseProfilePolarityRouteOperation

abbrev RouteBlock := DirectedClauseProfile × List (List AxisDirection)
abbrev RoutePair := FormulaShapeFigureNinePolarityRouteHeader.Header × List AxisDirection

def routeBlock (block : RouteBlock) : List RoutePair := sourceClausePairs block.1 block.2

theorem sourcePairs_blocks (blocks : List RouteBlock) :
    sourcePairs (blocks.map (fun block => Token.clause block.1)) (blocks.map Prod.snd) =
      blocks.flatMap routeBlock := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.map_cons, sourcePairs, List.flatMap_cons, List.headD_cons, List.tail_cons]
    rw [ih]
    rfl

theorem routeBlock_length (block : RouteBlock) :
    (routeBlock block).length = tokenSize (.clause block.1) := by
  simp only [routeBlock, sourceClausePairs, List.length_map, tokenSize]

theorem routeBlock_offsets_valid (block : RouteBlock) (i : Nat)
    (member : i ∈ tokenOffsets (.clause block.1)) : i < (routeBlock block).length := by
  change i ∈ (slots block.1).map (selectedIndex block.1) at member
  obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
  rw [routeBlock_length]
  exact selectedIndex_lt block.1 slot ((slots_active _ _).1 slotMember)

theorem selectedPair (block : RouteBlock) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < block.1.taggedLiterals.length) :
    (routeBlock block).getD (selectedIndex block.1 slot) default =
      (selectedHeader block.1 slot, selectedTailDirections block.2 (selectedHeader block.1 slot)) := by
  unfold routeBlock sourceClausePairs selectedHeader
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using selectedIndex_lt block.1 slot active),
    List.getElem_map, List.getD_eq_getElem _ _ (selectedIndex_lt block.1 slot active)]

theorem queryPairs (blocks : List RouteBlock) :
    (queries (blocks.map (fun block => Token.clause block.1))).map
      (fun i => (blocks.flatMap routeBlock).getD i default) =
      blocks.flatMap (fun block => (slots block.1).map (fun slot =>
        (selectedHeader block.1 slot, selectedTailDirections block.2 (selectedHeader block.1 slot)))) := by
  rw [queries, FiniteTemplateQueries.lookup_payload _ _ _ routeBlock blocks
    (fun block _ => routeBlock_length block) routeBlock_offsets_valid default]
  apply List.flatMap_congr
  intro block _
  simp only [tokenOffsets, List.map_map]
  apply List.map_congr_left
  intro slot member
  exact selectedPair block slot ((slots_active _ _).1 member)

theorem routeQueries_valid (blocks : List RouteBlock) (i : Nat)
    (member : i ∈ queries (blocks.map (fun block => Token.clause block.1))) :
    i < (blocks.flatMap routeBlock).length := by
  have valid : ∀ token j, j ∈ tokenOffsets token → j < tokenSize token := by
    intro token j member
    cases token with
    | «variable» => simp [tokenOffsets] at member
    | clause profile =>
      change j ∈ (slots profile).map (selectedIndex profile) at member
      obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
      exact selectedIndex_lt profile slot ((slots_active _ _).1 slotMember)
  have bound := (FiniteTemplateQueries.queriesFrom_bound tokenSize tokenOffsets valid _ 0 i member).2
  simpa only [List.map_map, Function.comp_def, List.length_flatMap, routeBlock_length, Nat.zero_add] using bound

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
