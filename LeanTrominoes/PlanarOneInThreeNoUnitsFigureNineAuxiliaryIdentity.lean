/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex

/-! # Global identity of instantiated Figure 9 auxiliary roles -/

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF.FormulaShapeFigureNineRoutePrefix

private def auxiliaryRole : OneInThreeAux → PlanarOneInThree.FigureNineVariable
  | .firstChoice => .firstChoice
  | .secondChoice => .secondChoice
  | .firstSlack => .firstSlack
  | .secondSlack => .secondSlack
  | .firstPadding => .firstPadding
  | .secondPadding => .secondPadding
  | .thirdPadding => .thirdPadding

private theorem auxiliaryRole_cases (role : FigureNineNoUnitsVariable)
    (auxiliary : sourceSlot? role = none) :
    (∃ kind, role = .inherited (auxiliaryRole kind)) ∨
      ∃ index kind, role = .unitAux index kind := by
  cases role with
  | inherited role =>
      left
      cases role <;> simp_all [sourceSlot?] <;> decide
  | unitAux index kind => exact Or.inr ⟨index, kind, rfl⟩

private theorem instantiatedVariableMap_auxiliaryRole
    {Variable : Type} (parent start : Nat) (source : PositionedPeriodicClause Variable)
    (kind : OneInThreeAux) :
    instantiatedVariableMap parent start source (.inherited (auxiliaryRole kind)) =
      .inl (.inr ((parent, source.literals), kind)) := by
  rcases source with ⟨position, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · cases kind <;> rfl
  · rcases rest with _ | ⟨second, rest⟩
    · cases kind <;> rfl
    · rcases rest with _ | ⟨third, rest⟩ <;> cases kind <;> rfl

/-- Equal instantiated auxiliaries recover their original parent and finite
role. Second-stage auxiliaries use genuine global first-stage metadata
lookups, so equal local indices in different parents cannot collide. -/
theorem instantiatedVariableMap_auxiliary_eq_iff
    {Variable : Type} (source : PositionedPeriodicCNF Variable)
    {first second : ClauseMetadata Variable}
    (firstMember : first ∈ formulaClauseMetadata source)
    (secondMember : second ∈ formulaClauseMetadata source)
    (firstRole secondRole : FigureNineNoUnitsVariable)
    (firstAuxiliary : sourceSlot? firstRole = none)
    (secondAuxiliary : sourceSlot? secondRole = none)
    (firstBound : ∀ index kind, firstRole = .unitAux index kind →
      index < (PeriodicOneInThreePositioned.clauseGadget first.sourceClauseIndex first.sourceClause).length)
    (secondBound : ∀ index kind, secondRole = .unitAux index kind →
      index < (PeriodicOneInThreePositioned.clauseGadget second.sourceClauseIndex second.sourceClause).length) :
    instantiatedVariableMap first.sourceClauseIndex first.figureNineClauseStart first.sourceClause firstRole =
        instantiatedVariableMap second.sourceClauseIndex second.figureNineClauseStart second.sourceClause secondRole ↔
      (first.sourceClauseIndex, firstRole) = (second.sourceClauseIndex, secondRole) := by
  constructor
  · intro atomsEq
    rcases auxiliaryRole_cases firstRole firstAuxiliary with ⟨firstKind, rfl⟩ | ⟨firstIndex, firstKind, rfl⟩ <;>
      rcases auxiliaryRole_cases secondRole secondAuxiliary with ⟨secondKind, rfl⟩ | ⟨secondIndex, secondKind, rfl⟩
    · simp only [instantiatedVariableMap_auxiliaryRole, Sum.inl.injEq, Sum.inr.injEq,
        Prod.mk.injEq] at atomsEq
      exact Prod.ext atomsEq.1.1 (by rw [atomsEq.2])
    · simp only [instantiatedVariableMap_auxiliaryRole, instantiatedVariableMap_unitAux] at atomsEq
      cases atomsEq
    · simp only [instantiatedVariableMap_auxiliaryRole, instantiatedVariableMap_unitAux] at atomsEq
      cases atomsEq
    · simp only [instantiatedVariableMap_unitAux, Sum.inr.injEq, Prod.mk.injEq] at atomsEq
      have firstLookup := formulaClauseMetadata_figureNineMetadata_lookup source firstMember
        (List.mk_mem_zipIdx_iff_getElem?.mpr
          (List.getElem?_eq_getElem (firstBound firstIndex firstKind rfl)))
      have secondLookup := formulaClauseMetadata_figureNineMetadata_lookup source secondMember
        (List.mk_mem_zipIdx_iff_getElem?.mpr
          (List.getElem?_eq_getElem (secondBound secondIndex secondKind rfl)))
      rw [atomsEq.1.1] at firstLookup
      have metadataEq := Option.some.inj (firstLookup.symm.trans secondLookup)
      have parentEq : first.sourceClauseIndex = second.sourceClauseIndex :=
        congrArg PeriodicOneInThreePositioned.ClauseMetadata.sourceClauseIndex metadataEq
      have indexEq : firstIndex = secondIndex :=
        congrArg PeriodicOneInThreePositioned.ClauseMetadata.localClauseIndex metadataEq
      exact Prod.ext parentEq (by rw [indexEq, atomsEq.2])
  · intro keysEq
    have parentEq : first.sourceClauseIndex = second.sourceClauseIndex := congrArg Prod.fst keysEq
    have roleEq : firstRole = secondRole := congrArg Prod.snd keysEq
    obtain ⟨sourceEq, startEq⟩ := formulaClauseMetadata_sourceBlock_eq
      source firstMember secondMember parentEq
    rw [parentEq, roleEq, sourceEq, startEq]

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
