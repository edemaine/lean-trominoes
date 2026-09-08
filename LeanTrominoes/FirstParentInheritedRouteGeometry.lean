/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FirstParentInheritedRouteSelection
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPresentationSlotSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderPrefixSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRouteOrderSemantics

/-! # The selected inherited tail belongs to the first presentation literal -/

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeaderPresentationAtomScope

/-- Selection always returns an actual generated header, never the fallback. -/
theorem selectedHeader_mem (profile : DirectedClauseProfile) :
    selectedHeader profile ∈ sourceClauseHeaders profile := by
  rw [selectedHeader, List.getD_eq_getElem _ _ (index_lt profile)]
  exact List.getElem_mem (index_lt profile)

theorem firstDirection_ofClause {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    firstDirection (DirectedClauseProfile.ofClause routes clauseIndex clause) =
      AxisDirection.polylineFirstDirection (routes clauseIndex 0) := by
  unfold firstDirection
  rw [DirectedClauseProfile.ofClause_taggedLiterals routes clauseIndex clause nonempty width]
  obtain ⟨literal, rest, literalsEq⟩ := List.exists_cons_of_ne_nil nonempty
  simp only [annotatedLiterals, literalsEq, List.zipIdx_cons, List.map_cons, List.headD_cons]

/-- The clockwise slot chosen by the header maps back to literal zero in the
original presentation, including when route directions tie. -/
theorem selectedTailDirections_ofClause {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    selectedTailDirections (orderedTailDirections routes clauseIndex clause)
        (selectedHeader (DirectedClauseProfile.ofClause routes clauseIndex clause)) =
      Gadget.unitSubdivisionDirections (routes clauseIndex 0).tail := by
  let profile := DirectedClauseProfile.ofClause routes clauseIndex clause
  obtain ⟨slot, query, prefixEq, presentationEq⟩ := selectedHeader_inherited profile
  obtain ⟨descriptorIndex, descriptorEq⟩ := exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
    profile (selectedHeader profile) (selectedHeader_mem profile)
  have active := PeriodicCNF.FormulaShapeFigureNineRoutePrefix.descriptorAt_inherited_sourceSlotNat_lt
    (orderedDirectedProfile profile) descriptorIndex slot query (descriptorEq.trans prefixEq)
  have slotLt : sourceSlotNat slot < clause.literals.length := by
    simpa only [profile, clauseProfile_orderedDirectedProfile,
      DirectedClauseProfile.orderedProfile_ofClause_literals routes clauseIndex clause nonempty width,
      PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles, PositionedPeriodicCNF.orderClauseByRouteDirection,
      PositionedPeriodicCNF.clauseLiteralOrder, List.length_map, List.length_insertionSort, List.length_zipIdx] using active
  have orderedLt : sourceSlotNat slot <
      (PositionedPeriodicCNF.clauseLiteralOrder routes clauseIndex clause).length := by
    simpa only [PositionedPeriodicCNF.clauseLiteralOrder, List.length_insertionSort, List.length_zipIdx] using slotLt
  have indexEq := presentationSlotAt_eq_clauseLiteralOrder_index routes clauseIndex clause nonempty width slot slotLt
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using orderedLt), List.getElem_map] at indexEq
  change sourceSlotNat (presentationSlotAt profile slot) = _ at indexEq
  rw [presentationEq] at indexEq
  change selectedTailDirections (orderedTailDirections routes clauseIndex clause) (selectedHeader profile) = _
  simp only [selectedTailDirections, prefixEq]
  rw [orderedTailDirections_eq_clauseLiteralOrder_map,
    List.getD_eq_getElem _ _ (by simpa only [List.length_map] using orderedLt), List.getElem_map, ← indexEq]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
