/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRoutes

/-! # Presentation indices of selected Figure 9 local routes -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- A genuine generated incidence retains its clause-major presentation
index when the instantiated Figure 9 drawing is related back to its finite
template.  This is the index needed by the finite route-prefix descriptor. -/
theorem localRoutes_eq_translated_templateRoute_with_index_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
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
        localRoutes source clauseIndex literalIndex =
          PeriodicOrthocrossing.translatePolyline
            (Cell.scale composedGadgetScale
              metadata.sourceClause.position)
            ((templateDrawing metadata.sourceClause).routeAt
              ((templateDrawing metadata.sourceClause).incidenceAt
                templateIndex)) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause :=
    instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  let incidence :
      EmbeddedCNFIncidence
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) :=
    ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
      metadata.localClauseIndex,
      (literal.atom, literal.value), literalIndex⟩
  have incidenceMember : incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
      ⟨embeddedClauseMember, embeddedLiteralMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  rcases instantiatedDrawing_routeAt_incidenceAt_eq
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause incidenceIndex with
    ⟨templateIndex, templateIndexValue, selectedRoute⟩
  refine ⟨metadata, incidenceIndex, templateIndex,
    metadataLookup, clauseEqual, ?_, templateIndexValue, ?_⟩
  · exact incidenceEqual
  · calc
      localRoutes source clauseIndex literalIndex =
          drawing.routes metadata.localClauseIndex literalIndex := by
        simp [localRoutes, metadataLookup, drawing]
      _ = drawing.routeAt (drawing.incidenceAt incidenceIndex) := by
        unfold EmbeddedCNFIncidenceDrawing.routeAt
          EmbeddedCNFIncidenceDrawing.incidenceAt
        rw [incidenceEqual]
      _ = _ := selectedRoute

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
