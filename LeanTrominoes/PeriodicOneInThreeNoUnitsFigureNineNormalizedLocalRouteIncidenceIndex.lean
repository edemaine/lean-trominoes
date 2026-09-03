/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRouteIncidenceIndex
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes

/-! # Presentation indices of normalized Figure 9 local routes -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Anchor normalization preserves the exact finite-template incidence index
and its clause/literal presentation coordinates. -/
theorem normalizedLocalRoutes_eq_translated_templateRoute_with_index_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ (metadata : ClauseMetadata Variable)
      (incidenceIndex : Fin
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).incidences.length)
      (templateIndex : Fin
        (templateDrawing metadata.sourceClause).incidences.length),
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).incidenceAt incidenceIndex =
            ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
              metadata.localClauseIndex,
              (literal.atom, literal.value), literalIndex⟩ ∧
        templateIndex.val = incidenceIndex.val ∧
        ((templateDrawing metadata.sourceClause).incidenceAt
          templateIndex).clauseIndex = metadata.localClauseIndex ∧
        ((templateDrawing metadata.sourceClause).incidenceAt
          templateIndex).literalIndex = literalIndex ∧
        normalizedLocalRoutes source sourcePlacement
            clauseIndex literalIndex =
          PeriodicOrthocrossing.translatePolyline
            (Cell.sub
              (Cell.scale composedGadgetScale
                metadata.sourceClause.position)
              ((composedPlacement source sourcePlacement).translation
                (PeriodicCNF.clauseAnchor metadata.clause.literals)))
            ((templateDrawing metadata.sourceClause).routeAt
              ((templateDrawing metadata.sourceClause).incidenceAt
                templateIndex)) := by
  rcases localRoutes_eq_translated_templateRoute_with_index_of_members
      source sourceWidth clauseMember literalMember with
    ⟨metadata, incidenceIndex, templateIndex,
      metadataLookup, metadataClause, incidenceEq, indexValue,
      clauseCoordinate, literalCoordinate, localEq⟩
  refine ⟨metadata, incidenceIndex, templateIndex,
    metadataLookup, metadataClause, incidenceEq, indexValue,
    clauseCoordinate, literalCoordinate, ?_⟩
  let anchor :=
    (composedPlacement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  let macroOrigin :=
    Cell.scale composedGadgetScale metadata.sourceClause.position
  let templateRoute :=
    (templateDrawing metadata.sourceClause).routeAt
      ((templateDrawing metadata.sourceClause).incidenceAt templateIndex)
  have composedTranslations :
      (PeriodicOrthocrossing.translatePolyline
          macroOrigin templateRoute).map
          (fun point => Cell.sub point anchor) =
        PeriodicOrthocrossing.translatePolyline
          (Cell.sub macroOrigin anchor) templateRoute := by
    unfold PeriodicOrthocrossing.translatePolyline
    rw [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    apply Prod.ext <;>
      simp [Cell.add, Cell.sub, sub_eq_add_neg, add_comm, add_assoc]
  simpa [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute,
    metadataClause, localEq, anchor, macroOrigin, templateRoute]
    using composedTranslations

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
