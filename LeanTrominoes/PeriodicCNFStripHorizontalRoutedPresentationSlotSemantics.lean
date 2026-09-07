/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixOrderedFanSemantics

/-! # Compiled presentation slots select actual clockwise source literals -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation

private abbrev IndexedLiteral :=
  (PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile × AxisDirection) × Nat

private def indexedDirectionLE (first second : IndexedLiteral) : Prop :=
  directionLE first.1 second.1

private instance : DecidableRel indexedDirectionLE := by
  intro first second
  unfold indexedDirectionLE
  infer_instance

private theorem presentationTaggedLiterals_map_indexed (profile : DirectedClauseProfile) :
    (presentationTaggedLiterals profile).map
        (fun tagged => (tagged.1, sourceSlotNat tagged.2)) =
      profile.taggedLiterals.zipIdx := by
  cases profile <;> rfl

/-- Stable finite-profile sorting retains exactly the original literal
indices used by the actual geometric clockwise sort, including direction ties. -/
theorem orderedPresentationSlots_eq_clauseLiteralOrder
    {Variable : Type} (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3) :
    (orderedPresentationSlots (DirectedClauseProfile.ofClause routes clauseIndex clause)).map sourceSlotNat =
      (PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).map Prod.snd := by
  let profile := DirectedClauseProfile.ofClause routes clauseIndex clause
  let finiteTag : TaggedLiteral → IndexedLiteral :=
    fun tagged => (tagged.1, sourceSlotNat tagged.2)
  let sourceTag : PeriodicLiteral Variable × Nat → IndexedLiteral :=
    fun tagged => ((literalProfile tagged.1,
      AxisDirection.polylineFirstDirection (routes clauseIndex tagged.2)), tagged.2)
  have finiteSort := List.map_insertionSort
    (r := taggedDirectionLE) (s := indexedDirectionLE) finiteTag
    (presentationTaggedLiterals profile) (by intro first _ second _; rfl)
  have sourceSort := List.map_insertionSort
    (r := PositionedPeriodicCNF.clauseLiteralDirectionLE routes clauseIndex)
    (s := indexedDirectionLE) sourceTag clause.literals.zipIdx
    (by intro first _ second _; rfl)
  have tagsEq : (presentationTaggedLiterals profile).map finiteTag =
      clause.literals.zipIdx.map sourceTag := by
    rw [show (presentationTaggedLiterals profile).map finiteTag =
      profile.taggedLiterals.zipIdx from presentationTaggedLiterals_map_indexed profile]
    rw [DirectedClauseProfile.ofClause_taggedLiterals routes clauseIndex clause nonempty width]
    exact List.zipIdx_map_zipIdx clause.literals _
  have sortedEq := finiteSort.trans
    ((congrArg (fun values => values.insertionSort indexedDirectionLE) tagsEq).trans sourceSort.symm)
  have indicesEq := congrArg (List.map Prod.snd) sortedEq
  simpa only [orderedPresentationSlots, orderedTaggedLiterals, PositionedPeriodicCNF.clauseLiteralOrder,
    List.map_map, Function.comp_def, finiteTag, sourceTag, profile] using indicesEq

/-- The executable presentation-slot query retrieves the original index of
the selected genuine clockwise literal. -/
theorem presentationSlotAt_eq_clauseLiteralOrder_index
    {Variable : Type} (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3)
    (slot : SourceLiteralSlot) (active : sourceSlotNat slot < clause.literals.length) :
    sourceSlotNat (presentationSlotAt (DirectedClauseProfile.ofClause routes clauseIndex clause) slot) =
      ((PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).map Prod.snd).getD
        (sourceSlotNat slot) 0 := by
  have finiteLt : sourceSlotNat slot <
      (orderedPresentationSlots (DirectedClauseProfile.ofClause routes clauseIndex clause)).length := by
    rw [orderedPresentationSlots_length,
      DirectedClauseProfile.ofClause_taggedLiterals routes clauseIndex clause nonempty width]
    simpa only [annotatedLiterals, List.length_map, List.length_zipIdx] using active
  rw [← orderedPresentationSlots_eq_clauseLiteralOrder routes clauseIndex clause nonempty width]
  rw [presentationSlotAt, List.getD_eq_getElem _ _ finiteLt,
    List.getD_eq_getElem _ _ (by simpa only [List.length_map] using finiteLt), List.getElem_map]

/-- At every active slot, the compiled inverse permutation selects exactly
the literal appearing in the actual clockwise clause. -/
theorem orderClause_literal_lookup_at_presentationSlot
    {Variable : Type} (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3)
    (slot : SourceLiteralSlot) (active : sourceSlotNat slot < clause.literals.length) :
    (PositionedPeriodicCNF.orderClauseByRouteDirection routes clauseIndex clause).literals[
        sourceSlotNat slot]? =
      clause.literals[sourceSlotNat
        (presentationSlotAt (DirectedClauseProfile.ofClause routes clauseIndex clause) slot)]? := by
  have orderedLt : sourceSlotNat slot <
      (PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).length := by
    simpa only [PositionedPeriodicCNF.clauseLiteralOrder, List.length_insertionSort,
      List.length_zipIdx] using active
  let tagged := (PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause)[sourceSlotNat slot]
  have taggedMember : tagged ∈ clause.literals.zipIdx :=
    (List.mem_insertionSort (r := PositionedPeriodicCNF.clauseLiteralDirectionLE routes clauseIndex)).mp
      (List.getElem_mem orderedLt)
  have literalLookup : clause.literals[tagged.2]? = some tagged.1 :=
    List.mk_mem_zipIdx_iff_getElem?.mp taggedMember
  have indexEq : sourceSlotNat
      (presentationSlotAt (DirectedClauseProfile.ofClause routes clauseIndex clause) slot) = tagged.2 := by
    rw [presentationSlotAt_eq_clauseLiteralOrder_index routes clauseIndex clause nonempty width slot active,
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using orderedLt), List.getElem_map]
  rw [indexEq, literalLookup]
  simp only [PositionedPeriodicCNF.orderClauseByRouteDirection, List.getElem?_map,
    List.getElem?_eq_getElem orderedLt, Option.map_some, tagged]

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
