/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixSourceSlotSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderPrefixSemantics
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineSelector

/-! # Source-slot classification under Figure 9 template instantiation -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- The descriptor's case and slot are exactly the classification of its
selected local-template atom. -/
theorem sourceSlot_descriptorAt
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (index : Fin (templateDrawingOfClauseProfile (clauseProfile profile)).incidences.length) :
    let descriptor := descriptorAt profile index
    let query := descriptor.localQuery
    sourceSlot? ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      match descriptor with
      | .local _ => none
      | .inherited slot _ => some slot := by
  dsimp only
  rw [localQuery_descriptorAt]
  unfold descriptorAt
  dsimp only
  cases sourceSlot? ((templateDrawingOfClauseProfile (clauseProfile profile)).incidenceAt
    index).literal.1 <;> rfl

/-- Every genuine header preserves that classification through the final
literal reordering and polarity-header expansion. -/
theorem sourceSlot_header
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (header : Header) (member : header ∈ sourceClauseHeaders profile) :
    let query := header.figurePrefix.localQuery
    sourceSlot? ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      match header.figurePrefix with
      | .local _ => none
      | .inherited slot _ => some slot := by
  obtain ⟨index, descriptorEq⟩ :=
    exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders profile header member
  rw [← descriptorEq]
  exact sourceSlot_descriptorAt _ index

/-- A finite auxiliary role remains auxiliary under actual-variable
instantiation, so it cannot acquire an inherited source-route tail. -/
theorem instantiatedVariableMap_not_inherited_of_sourceSlot_none
    {Variable : Type}
    (parent start : Nat) (source : PositionedPeriodicClause Variable)
    (role : FigureNineNoUnitsVariable) (selected : sourceSlot? role = none)
    (atom : Variable) :
    instantiatedVariableMap parent start source role ≠ .inl (.inl atom) := by
  cases role with
  | unitAux localIndex kind => simp
  | inherited role =>
    rcases source with ⟨position, literals⟩
    rcases literals with _ | ⟨first, rest⟩
    · cases role <;> simp_all [sourceSlot?, instantiatedVariableMap,
        zeroVariableMap, variableMap, zeroInheritedMap]
    · rcases rest with _ | ⟨second, rest⟩
      · cases role <;> simp_all [sourceSlot?, instantiatedVariableMap,
          oneVariableMap, variableMap, oneInheritedMap]
      · rcases rest with _ | ⟨third, tail⟩
        · cases role <;> simp_all [sourceSlot?, instantiatedVariableMap,
            twoVariableMap, variableMap, twoInheritedMap]
        · cases role <;> simp_all [sourceSlot?, instantiatedVariableMap,
            threeVariableMap, variableMap, threeInheritedMap]

/-- At an active inherited slot, instantiation selects exactly the source
literal's atom at that slot, including its occurrence index. -/
theorem instantiatedVariableMap_of_sourceSlot_some
    {Variable : Type}
    (parent start : Nat) (source : PositionedPeriodicClause Variable)
    (role : FigureNineNoUnitsVariable) (slot : SourceLiteralSlot)
    (selected : sourceSlot? role = some slot)
    (active : sourceSlotNat slot < source.literals.length) :
    instantiatedVariableMap parent start source role =
      .inl (.inl source.literals[sourceSlotNat slot].atom) := by
  have roleEq : role = (match slot with
      | .first => .inherited .sourceFirst
      | .second => .inherited .sourceSecond
      | .third => .inherited .sourceThird) := by
    cases role with
    | unitAux localIndex kind => simp [sourceSlot?] at selected
    | inherited role =>
      cases role <;> cases slot <;> first | rfl | simp [sourceSlot?] at selected
  rw [roleEq]
  rcases source with ⟨position, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp at active
  · rcases rest with _ | ⟨second, rest⟩
    · cases slot <;> simp [sourceSlotNat] at active <;> simp [sourceSlotNat, instantiatedVariableMap,
        oneVariableMap, variableMap, oneInheritedMap]
    · rcases rest with _ | ⟨third, tail⟩
      · cases slot <;> simp [sourceSlotNat] at active <;> simp [sourceSlotNat, instantiatedVariableMap,
          twoVariableMap, variableMap, twoInheritedMap]
      · cases slot <;> simp [sourceSlotNat] at active <;> simp [sourceSlotNat, instantiatedVariableMap,
          threeVariableMap, variableMap, threeInheritedMap]

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix
