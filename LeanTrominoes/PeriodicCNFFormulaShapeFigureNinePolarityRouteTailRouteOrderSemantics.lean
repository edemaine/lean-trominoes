/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingClauseSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixSourceSlotSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailRouteOrderSemantics

/-! # Figure 9 route-tail selection follows canonical route order -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTail

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNineSourceTail
open Gadget

private theorem orderedClauseProfile_length
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    (clauseProfile
      (orderedDirectedProfile
        (DirectedClauseProfile.ofClause
          routes clauseIndex clause))).literals.length =
      clause.literals.length := by
  rw [clauseProfile_orderedDirectedProfile,
    DirectedClauseProfile.orderedProfile_ofClause_literals
      routes clauseIndex clause nonempty width]
  simp [ClauseProfileOccurrenceSplit.literalProfiles]

/-- When an inherited finite prefix selects one original source slot, the
paired dynamic tail is exactly the tail word of that slot in the canonical
clockwise route family. -/
theorem selectedTailDirections_descriptorAt_inherited_eq_canonicalRoute
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3)
    (polarity : ClauseProfilePolarityRouteOperation.Descriptor)
    (index : Fin
      (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        (clauseProfile
          (orderedDirectedProfile
            (DirectedClauseProfile.ofClause
              routes clauseIndex clause)))).incidences.length)
    (sourceSlot : SourceLiteralSlot)
    (query : PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery)
    (descriptorEq :
      descriptorAt
          (orderedDirectedProfile
            (DirectedClauseProfile.ofClause routes clauseIndex clause))
          index =
        .inherited sourceSlot query) :
    selectedTailDirections
        (orderedTailDirections routes clauseIndex clause)
        ⟨polarity,
          descriptorAt
            (orderedDirectedProfile
              (DirectedClauseProfile.ofClause routes clauseIndex clause))
            index⟩ =
      unitSubdivisionDirections
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes clauseIndex
            (sourceSlotNat sourceSlot)).tail := by
  unfold selectedTailDirections
  rw [descriptorEq]
  rw [orderedTailDirections_eq_map_range_orderCanonicalRoutes
    source placement routes clauseIndex clause clauseLookup]
  have sourceSlotLtProfile :=
    descriptorAt_inherited_sourceSlotNat_lt
      (orderedDirectedProfile
        (DirectedClauseProfile.ofClause routes clauseIndex clause))
      index sourceSlot query descriptorEq
  have sourceSlotLt : sourceSlotNat sourceSlot < clause.literals.length := by
    rw [← orderedClauseProfile_length
      routes clauseIndex clause nonempty width]
    exact sourceSlotLtProfile
  have mappedLt : sourceSlotNat sourceSlot <
      ((List.range clause.literals.length).map fun literalIndex =>
        unitSubdivisionDirections
          (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
            source placement routes clauseIndex literalIndex).tail).length := by
    simpa using sourceSlotLt
  change
    ((List.range clause.literals.length).map fun literalIndex =>
      unitSubdivisionDirections
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes clauseIndex literalIndex).tail).getD
        (sourceSlotNat sourceSlot) [] =
      unitSubdivisionDirections
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes clauseIndex
            (sourceSlotNat sourceSlot)).tail
  rw [List.getD_eq_getElem _ _ mappedLt, List.getElem_map,
    List.getElem_range]

end FormulaShapeFigureNinePolarityRouteTail
end PeriodicCNF
end LeanTrominoes
