/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData

/-! # Source-slot validity of Figure 9 prefix descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeFigureNinePolarityRouteHeader
open UnaryProgramClauseProfile

private theorem sourceSlot?_incidenceAt_some_lt
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (index : Fin
      (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length)
    (sourceSlot : SourceLiteralSlot)
    (sourceSlotEq : sourceSlot?
      ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        (clauseProfile profile)).incidenceAt index).literal.1 =
          some sourceSlot) :
    sourceSlotNat sourceSlot < (clauseProfile profile).literals.length := by
  cases profile <;> native_decide +revert

/-- Every inherited finite-template descriptor names an active literal slot
of the source clause profile. -/
theorem descriptorAt_inherited_sourceSlotNat_lt
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (index : Fin
      (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length)
    (sourceSlot : SourceLiteralSlot)
    (query : PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery)
    (descriptorEq : descriptorAt profile index =
      .inherited sourceSlot query) :
    sourceSlotNat sourceSlot < (clauseProfile profile).literals.length := by
  let incidence :=
    (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
      (clauseProfile profile)).incidenceAt index
  cases sourceSlotEq : sourceSlot? incidence.literal.1 with
  | none =>
      simp [descriptorAt, incidence, sourceSlotEq] at descriptorEq
  | some actualSourceSlot =>
      have actualEq : actualSourceSlot = sourceSlot := by
        have optionEq := congrArg
          (fun descriptor => match descriptor with
            | Descriptor.local _ => none
            | Descriptor.inherited selected _ => some selected)
          descriptorEq
        simp only [descriptorAt, incidence, sourceSlotEq] at optionEq
        change some actualSourceSlot = some sourceSlot at optionEq
        exact Option.some.inj optionEq
      subst sourceSlot
      exact sourceSlot?_incidenceAt_some_lt
        profile index actualSourceSlot (by
          simpa only [incidence] using sourceSlotEq)

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
